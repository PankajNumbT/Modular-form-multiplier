import streamlit as st
import pandas as pd
import time
import re
import math
from fractions import Fraction
from itertools import product
from functools import reduce

# ==========================================
# --- SHARED MATH ENGINE & PARSER ---
# ==========================================

class QSeries:
    def __init__(self, coeffs, limit):
        self.coeffs = list(coeffs)
        self.limit = limit
        if len(self.coeffs) < limit + 1:
            self.coeffs += [0] * (limit + 1 - len(self.coeffs))

    def __add__(self, other):
        if isinstance(other, (int, float)):
            new_coeffs = list(self.coeffs)
            new_coeffs[0] += int(other)
            return QSeries(new_coeffs, self.limit)
        return QSeries([a + b for a, b in zip(self.coeffs, other.coeffs)], self.limit)

    def __radd__(self, other): return self.__add__(other)

    def __sub__(self, other):
        if isinstance(other, (int, float)):
            new_coeffs = list(self.coeffs)
            new_coeffs[0] -= int(other)
            return QSeries(new_coeffs, self.limit)
        return QSeries([a - b for a, b in zip(self.coeffs, other.coeffs)], self.limit)

    def __rsub__(self, other):
        return QSeries([-c for c in self.coeffs], self.limit) + other

    def __mul__(self, other):
        if isinstance(other, (int, float)):
            return QSeries([c * int(other) for c in self.coeffs], self.limit)
        C = [0] * (self.limit + 1)
        A_nonzeros = [(i, val) for i, val in enumerate(self.coeffs) if val != 0]
        for j, b_val in enumerate(other.coeffs):
            if b_val == 0: continue
            for i, a_val in A_nonzeros:
                if i + j <= self.limit:
                    C[i + j] += a_val * b_val
        return QSeries(C, self.limit)

    def __rmul__(self, other): return self.__mul__(other)

    def inv(self):
        B = [0] * (self.limit + 1)
        B[0] = 1 
        for n in range(1, self.limit + 1):
            sum_val = sum(self.coeffs[k] * B[n - k] for k in range(1, n + 1) if self.coeffs[k] != 0)
            B[n] = -sum_val
        return QSeries(B, self.limit)

    def __pow__(self, power):
        if power == 0:
            C = [0] * (self.limit + 1); C[0] = 1
            return QSeries(C, self.limit)
        base = self.inv() if power < 0 else self
        p = abs(power)
        res = QSeries([1] + [0]*self.limit, self.limit)
        current_pow = base
        while p > 0:
            if p % 2 == 1: res = res * current_pow
            current_pow = current_pow * current_pow
            p //= 2
        return res
        
    def __truediv__(self, other):
        if isinstance(other, QSeries): return self * other.inv()
        elif isinstance(other, (int, float)): return QSeries([c // int(other) for c in self.coeffs], self.limit)

@st.cache_data(show_spinner=False)
def generate_base_pochhammer(m, limit):
    A = [0] * (limit + 1); A[0] = 1; k = 1
    while True:
        p1 = m * k * (3 * k - 1) // 2
        p2 = m * k * (3 * k + 1) // 2
        sign = -1 if k % 2 != 0 else 1
        if p1 <= limit: A[p1] = sign
        if p2 <= limit: A[p2] = sign
        if p1 > limit and p2 > limit: break
        k += 1
    return A

def latex_to_python(latex_str):
    s = latex_str.replace('$', '').replace('\r', '').replace('\n', '')
    while r'\frac' in s:
        start_idx = s.find(r'\frac')
        idx = start_idx + 5
        def get_group(start_i):
            if start_i >= len(s): return "1", start_i
            if s[start_i] != '{': return s[start_i], start_i
            count = 1; i = start_i + 1
            while count > 0 and i < len(s):
                if s[i] == '{': count += 1
                elif s[i] == '}': count -= 1
                i += 1
            return s[start_i+1:i-1], i-1
        num, num_end = get_group(idx)
        den, den_end = get_group(num_end + 1)
        s = s[:start_idx] + f"(({num})/({den}))" + s[den_end+1:]
        
    s = re.sub(r'f_\{([^\}]+)\}', r'f(\1)', s)
    s = re.sub(r'f_(\d+|[a-zA-Z])', r'f(\1)', s)
    
    s = s.replace('^', '**').replace('{', '(').replace('}', ')')
    s = s.replace(r'\cdot', '*').replace(r'\times', '*').replace(r'\left(', '(').replace(r'\right)', ')')
    s = s.replace(' ', '') 
    
    s = s.replace('x', 'X')
    
    s = re.sub(r'\)([a-zA-Z])', r')*\1', s)       
    s = re.sub(r'(\d)([a-zA-Z])', r'\1*\2', s)    
    s = re.sub(r'([qX])([fXq])', r'\1*\2', s)     
    s = re.sub(r'([f])([qX])', r'\1*\2', s)       
    s = re.sub(r'\)\(', r')*(', s)                
    s = re.sub(r'([qX])\(', r'\1*(', s)           
    s = re.sub(r'\)(\d)', r')*\1', s)             
    
    s = re.sub(r'(f\([^)]+\))(f\()', r'\1*\2', s)
    
    return s

def lcm(a, b): return abs(a*b) // math.gcd(a, b) if a and b else 0
def lcm_list(lst): return reduce(lcm, lst, 1) if lst else 1


# ==========================================
# --- SYMBOLIC ALGEBRA ENGINE ---
# ==========================================

class SymTerm:
    def __init__(self, coeff=1, q_power=0, etas=None):
        self.coeff = Fraction(coeff)
        self.q_power = q_power
        self.etas = {int(k): int(v) for k, v in (etas or {}).items() if v != 0}

    def key(self): return (self.q_power, frozenset(self.etas.items()))

    def substitute_q(self, m):
        if m == 1: return self
        new_etas = {k * m: v for k, v in self.etas.items()}
        return SymTerm(self.coeff, self.q_power * m, new_etas)

    def simplify_mod(self, p):
        if p < 2: return self
        # 1. Push all eta bases down (e.g. f_pk -> f_k^p) to find common coprime basis
        base_etas = {}
        for k, v in self.etas.items():
            curr_k, curr_v = k, v
            while curr_k % p == 0:
                curr_k //= p
                curr_v *= p
            base_etas[curr_k] = base_etas.get(curr_k, 0) + curr_v
        
        # 2. Push bases back up mod p using division towards zero to prevent infinite loops
        final_etas = {}
        for k, v in base_etas.items():
            curr_k, curr_v = k, v
            while curr_v != 0:
                q = int(curr_v / p)
                r = curr_v - q * p
                if r != 0:
                    final_etas[curr_k] = final_etas.get(curr_k, 0) + r
                curr_v = q
                curr_k *= p
                
        new_etas = {k: v for k, v in final_etas.items() if v != 0}
        # Intentionally preserving the exact integer coefficient as requested
        return SymTerm(self.coeff, self.q_power, new_etas)

    def __mul__(self, other):
        if isinstance(other, (int, float, Fraction)): return SymTerm(self.coeff * other, self.q_power, self.etas)
        c = self.coeff * other.coeff
        q = self.q_power + other.q_power
        e = self.etas.copy()
        for k, v in other.etas.items(): e[k] = e.get(k, 0) + v
        return SymTerm(c, q, e)

    def __rmul__(self, other): return self.__mul__(other)
    
    def __truediv__(self, other):
        if isinstance(other, (int, float, Fraction)): return SymTerm(self.coeff / other, self.q_power, self.etas)
        c = self.coeff / other.coeff
        q = self.q_power - other.q_power
        e = self.etas.copy()
        for k, v in other.etas.items(): e[k] = e.get(k, 0) - v
        return SymTerm(c, q, e)

    def __rtruediv__(self, other): return SymTerm(other / self.coeff, -self.q_power, {k: -v for k, v in self.etas.items()})

    def __pow__(self, power): return SymTerm(self.coeff**power, self.q_power*power, {k: v*power for k, v in self.etas.items()})

    def to_latex(self):
        if self.coeff == 0: return ""
        c_str = "+" if self.coeff > 0 else "-"
        abs_c = abs(self.coeff)
        q_str = "q" if self.q_power == 1 else (f"q^{{{self.q_power}}}" if self.q_power != 0 else "")
            
        num, den = [], []
        for d in sorted(self.etas.keys()):
            p = self.etas[d]
            if p == 1: num.append(f"f_{{{d}}}")
            elif p > 1: num.append(f"f_{{{d}}}^{{{p}}}")
            elif p == -1: den.append(f"f_{{{d}}}")
            elif p < -1: den.append(f"f_{{{d}}}^{{{-p}}}")
            
        num_str = " ".join(num)
        den_str = " ".join(den)
        
        if isinstance(self.coeff, Fraction) and self.coeff.denominator != 1:
            n, d = self.coeff.numerator, self.coeff.denominator
            top = f"{abs(n)} {q_str} {num_str}".strip() if num_str or q_str else str(abs(n))
            if top.startswith("1 ") and not top == "1": top = top[2:]
            bot = f"{d} {den_str}".strip()
            return f"{c_str}\\frac{{{top}}}{{{bot}}}"
        else:
            top = f"{abs_c} {q_str} {num_str}".strip() if num_str or q_str else str(abs_c)
            if top.startswith("1 ") and not top == "1": top = top[2:]
            if den_str: return f"{c_str}\\frac{{{top}}}{{{den_str}}}"
            else: return f"{c_str}{top}"

class SymExpr:
    def __init__(self, terms):
        self.terms = [terms] if isinstance(terms, SymTerm) else terms
        self.simplify()

    def simplify(self):
        grouped = {}
        for t in self.terms:
            k = t.key()
            if k not in grouped: grouped[k] = SymTerm(0, t.q_power, t.etas)
            grouped[k].coeff += t.coeff
        self.terms = [t for t in grouped.values() if t.coeff != 0]
        self.terms.sort(key=lambda t: (t.q_power, sum(t.etas.values())))

    def substitute_q(self, m):
        if m == 1: return self
        return SymExpr([t.substitute_q(m) for t in self.terms])
        
    def simplify_mod(self, p):
        if p < 2: return self
        return SymExpr([t.simplify_mod(p) for t in self.terms])

    def __add__(self, other):
        if isinstance(other, (int, float, Fraction)):
            if other == 0: return self
            return SymExpr(self.terms + [SymTerm(other)])
        if isinstance(other, SymTerm): return SymExpr(self.terms + [other])
        return SymExpr(self.terms + other.terms)

    def __radd__(self, other): return self.__add__(other)
    def __sub__(self, other): return self + (other * -1)
    def __rsub__(self, other): return (self * -1) + other

    def __mul__(self, other):
        if isinstance(other, (int, float, Fraction)): return SymExpr([t * other for t in self.terms])
        if isinstance(other, SymTerm): return SymExpr([t * other for t in self.terms])
        new_terms = []
        for t1 in self.terms:
            for t2 in other.terms: new_terms.append(t1 * t2)
        return SymExpr(new_terms)

    def __rmul__(self, other): return self.__mul__(other)
    
    def __truediv__(self, other):
        if isinstance(other, (int, float, Fraction)) or isinstance(other, SymTerm): return SymExpr([t / other for t in self.terms])
        if isinstance(other, SymExpr) and len(other.terms) == 1: return SymExpr([t / other.terms[0] for t in self.terms])
        raise ValueError("Cannot divide by a complex sum in algebraic mode.")

    def __rtruediv__(self, other):
        if len(self.terms) == 1: return SymExpr([other / self.terms[0]])
        raise ValueError("Cannot divide by a sum of terms.")

    def __pow__(self, power):
        if not isinstance(power, int) or power < 0: raise ValueError("Power must be a non-negative integer.")
        if power == 0: return SymExpr([SymTerm(1)])
        res, base = SymExpr([SymTerm(1)]), SymExpr(self.terms)
        for _ in range(power): res = res * base
        return res

    def to_latex(self):
        if not self.terms: return "0"
        res = ""
        for i, t in enumerate(self.terms):
            t_lat = t.to_latex()
            if i == 0: res += t_lat[1:] if t_lat.startswith("+") else t_lat
            else:
                if t_lat.startswith("-"): res += f" - {t_lat[1:]}"
                else: res += f" + {t_lat[1:]}"
        return res.strip()

def scale_latex_lhs(s, m):
    if m == 1: return s
    s = re.sub(r'f_\{(\d+)\}', lambda x: f"f_{{{int(x.group(1))*m}}}", s)
    s = re.sub(r'f_(\d+)', lambda x: f"f_{{{int(x.group(1))*m}}}", s)
    return s

# ==========================================
# --- MODULE 3/5 SPECIFIC MATH ENGINE ---
# ==========================================

class EtaDictTerm:
    def __init__(self, terms=None): self.terms = terms if terms is not None else {}
    def __mul__(self, other):
        if isinstance(other, (int, float)): return self
        new_terms = self.terms.copy()
        for d, p in other.terms.items(): new_terms[d] = new_terms.get(d, 0) + p
        return EtaDictTerm(new_terms)
    def __rmul__(self, other): return self
    def __truediv__(self, other):
        if isinstance(other, (int, float)): return self
        new_terms = self.terms.copy()
        for d, p in other.terms.items(): new_terms[d] = new_terms.get(d, 0) - p
        return EtaDictTerm(new_terms)
    def __rtruediv__(self, other): return EtaDictTerm({d: -p for d, p in self.terms.items()})
    def __pow__(self, power): return EtaDictTerm({d: p * power for d, p in self.terms.items()})

def get_divisors(n): return [d for d in range(1, n + 1) if n % d == 0]

def constrained_partitions(n, k):
    if n == 1: yield [k]; return
    for i in range(k + 1):
        for p in constrained_partitions(n - 1, k - i): yield [i] + p

def get_sturm_bound(k, N):
    index, temp_n, d, primes = N, N, 2, set()
    while d * d <= temp_n:
        if temp_n % d == 0:
            primes.add(d)
            while temp_n % d == 0: temp_n //= d
        d += 1
    if temp_n > 1: primes.add(temp_n)
    for p in primes: index = index * (1 + 1/p)
    return math.ceil((k * index) / 12)

def compute_euler_exponents(c_array, max_terms):
    W = [Fraction(0)] * (max_terms + 1)
    for m in range(1, max_terms + 1):
        sum_W_c = sum(W[k] * c_array[m - k] for k in range(1, m))
        W[m] = m * c_array[m] - sum_W_c
    a = [Fraction(0)] * (max_terms + 1)
    for n in range(1, max_terms + 1):
        sum_mu_W = Fraction(0)
        for d in range(1, n + 1):
            if n % d == 0: sum_mu_W += get_moebius(n // d) * W[d]
        a[n] = sum_mu_W / n 
    return [int(x) if x.denominator == 1 else float(x) for x in a]

# ==========================================
# --- MODULE 1: CONGRUENCE MINER ---
# ==========================================

def run_congruence_miner():
    st.title("⛏️ Absolute $q$-Series Congruence Miner")
    st.markdown("Search for modular congruences and export directly to LaTeX.")

    with st.sidebar:
        st.header("⚙️ 1. Series Definition")
        st.info("Supports $q^k$ shifts, integers, and parametric families using capital **X**! \nExample: `\\frac{f_2 f_{3X}}{f_1 f_{3X}}`")
        latex_input = st.text_area("Enter LaTeX Formula:", value=r"\frac{f_2 f_{3X}}{f_1 f_{3X}}", height=80)
        st.latex(latex_input)
        st.divider()
        
        st.header("🔍 2. Analysis Mode")
        mode = st.radio("Select Tool:", ["Single Pattern Check", "Full Progression Sweep", "Hunter Mode (Run until found)", "Parametric Family Search (Variable X)"])
        st.divider()
        
        if mode == "Single Pattern Check":
            col_k, col_r, col_M = st.columns(3)
            A_val = col_k.number_input("k", min_value=1, value=5)
            B_val = col_r.number_input("r", min_value=0, value=4)
            M_val = col_M.number_input("M", min_value=1, value=5)
        elif mode == "Full Progression Sweep":
            col_k, col_M = st.columns(2)
            sweep_k = col_k.number_input("Stride (k)", min_value=2, value=5)
            sweep_M = col_M.number_input("Modulus (M)", min_value=2, value=5)
        elif mode == "Parametric Family Search (Variable X)":
            col_min, col_max = st.columns(2)
            x_min = col_min.number_input("X Start", value=1)
            x_max = col_max.number_input("X End", value=5)
            hunt_M = st.number_input("Target Modulus (M)", min_value=2, value=5)
            hunt_max = st.number_input("Stop Limit (Max stride k)", min_value=2, value=20)
        else:
            hunt_M = st.number_input("Target Modulus (M)", min_value=2, value=5)
            hunt_strategy = st.radio("Hunting Strategy:", ["Stop at First Match", "Collect Multiple Matches"])
            hunt_bounty_limit = st.number_input("Max Bounties", min_value=2, value=10) if hunt_strategy == "Collect Multiple Matches" else 1 
            hunt_max = st.number_input("Stop Limit (Max stride k)", min_value=2, value=100)
            
        st.divider()
        limit = st.number_input("Max power of q to compute (N)", min_value=100, value=3000, step=100)
        run_btn = st.button("🚀 Run Miner Analysis", type="primary", use_container_width=True)

    if run_btn:
        start_time = time.time()
        def f(n): 
            if int(n) <= 0: return QSeries([1] + [0]*limit, limit)
            return QSeries(generate_base_pochhammer(int(n), limit), limit)
        q_obj = QSeries([0, 1] + [0]*limit, limit)
        python_formula = latex_to_python(latex_input)
        
        try:
            if mode == "Parametric Family Search (Variable X)":
                family_results = []
                with st.spinner(f"Scanning parameterized family for X from {x_min} to {x_max}..."):
                    for x_val in range(int(x_min), int(x_max) + 1):
                        safe_env = {"f": f, "q": q_obj, "X": x_val, "__builtins__": {}}
                        try:
                            final_series = eval(python_formula, safe_env)
                            if not isinstance(final_series, QSeries): final_series = QSeries([int(final_series)] + [0]*limit, limit)
                            F_q = final_series.coeffs
                            found_for_x = []
                            for current_k in range(2, hunt_max + 1):
                                for r in range(current_k):
                                    max_n = (limit - r) // current_k
                                    if max_n < 5: continue 
                                    is_congruent = True
                                    for n_val in range(max_n + 1):
                                        if current_k * n_val + r <= limit and F_q[current_k * n_val + r] % hunt_M != 0:
                                            is_congruent = False; break
                                    if is_congruent: found_for_x.append(f"c({current_k}n + {r}) ≡ 0")
                            if found_for_x: family_results.append({"X Value": x_val, f"Congruences mod {hunt_M}": ", ".join(found_for_x)})
                            else: family_results.append({"X Value": x_val, f"Congruences mod {hunt_M}": "None found within limits"})
                        except Exception as e: family_results.append({"X Value": x_val, f"Congruences mod {hunt_M}": f"Math Error: {e}"})
                st.divider()
                st.subheader(f"📊 Parametric Analysis Complete")
                st.table(pd.DataFrame(family_results))

            else:
                safe_env = {"f": f, "q": q_obj, "X": 1, "__builtins__": {}}
                with st.spinner(f"Computing Series Expansion O(q^{limit})..."):
                    final_series = eval(python_formula, safe_env)
                    if not isinstance(final_series, QSeries): final_series = QSeries([int(final_series)] + [0]*limit, limit)
                    F_q = final_series.coeffs
                st.divider()
                st.subheader("📊 Analysis Results")
                    
                if mode == "Single Pattern Check":
                    success_count, total_checked, failures = 0, 0, []
                    max_n = (limit - B_val) // A_val
                    for n_val in range(max_n + 1):
                        idx = A_val * n_val + B_val
                        if idx > limit: break
                        total_checked += 1
                        if F_q[idx] % M_val == 0: success_count += 1
                        else: failures.append({"n": n_val, f"Power of q": idx, "Coefficient": F_q[idx], f"Mod {M_val}": F_q[idx] % M_val})
                    if not failures: 
                        st.success(f"🎉 **Verified!** All {total_checked} coefficients satisfy the congruence.")
                        st.code(rf"c({A_val}n + {B_val}) \equiv 0 \pmod{{{M_val}}}", language="latex")
                    else:
                        st.warning(f"⚠️ Failed modulo {M_val} test.")
                        st.dataframe(pd.DataFrame(failures[:50]), use_container_width=True)
                        
                elif mode == "Full Progression Sweep":
                    found_congruences = []
                    with st.spinner("Testing all remainders..."):
                        for r in range(sweep_k):
                            max_n = (limit - r) // sweep_k
                            if max_n < 5: continue 
                            is_congruent = True
                            for n_val in range(max_n + 1):
                                if sweep_k * n_val + r <= limit and F_q[sweep_k * n_val + r] % sweep_M != 0:
                                    is_congruent = False; break
                            if is_congruent: found_congruences.append((sweep_k, r, max_n + 1))
                    if not found_congruences: st.info(f"No congruences modulo {sweep_M} found for k={sweep_k}.")
                    else:
                        st.success(f"🎉 Discovered {len(found_congruences)} valid congruence(s) modulo {sweep_M}!")
                        st.table(pd.DataFrame([{"Pattern": f"c({k}n + {r}) ≡ 0", "Modulus": f"mod {sweep_M}", "Checked up to": f"n = {t-1}"} for k, r, t in found_congruences]))
                        for k, r, _ in found_congruences: st.code(rf"c({k}n + {r}) \equiv 0 \pmod{{{sweep_M}}}", language="latex")

                else:
                    found_matches = []
                    with st.spinner(f"Hunting for congruences modulo {hunt_M}..."):
                        for current_k in range(2, hunt_max + 1):
                            for r in range(current_k):
                                max_n = (limit - r) // current_k
                                if max_n < 5: continue 
                                is_congruent = True
                                for n_val in range(max_n + 1):
                                    if current_k * n_val + r <= limit and F_q[current_k * n_val + r] % hunt_M != 0:
                                        is_congruent = False; break
                                if is_congruent:
                                    found_matches.append({"k": current_k, "r": r, "terms": max_n + 1})
                                    if len(found_matches) >= hunt_bounty_limit: break
                            if len(found_matches) >= hunt_bounty_limit: break
                    if found_matches:
                        st.success(f"🎯 **HUNT FINISHED!** Mined {len(found_matches)} congruences.")
                        st.table(pd.DataFrame([{"Pattern": f"c({hit['k']}n + {hit['r']}) ≡ 0", "Modulus": f"mod {hunt_M}", "Verified up to": f"n = {hit['terms'] - 1}"} for hit in found_matches]))
                        for hit in found_matches: st.code(rf"c({hit['k']}n + {hit['r']}) \equiv 0 \pmod{{{hunt_M}}}", language="latex")
                    else:
                        st.error(f"❌ **Hunt Exhausted.** Zero congruences modulo {hunt_M} were found up to k = {hunt_max}.")
                        
                with st.expander("Show first 50 coefficients of the computed series"):
                    st.write(F_q[:50])

        except NameError as e:
            st.error(f"❌ **Variable Error:** `{e}`. Make sure to use capital 'X' for variables.")
        except SyntaxError as e:
            st.error(f"❌ **Syntax Error in formula:** `{e}`. Parser converted it to: `{python_formula}`")
        except Exception as e: 
            st.error(f"❌ **Failed to evaluate expression:** {e}")

# ==========================================
# --- MODULE 2: EULER PRODUCT EXPLORER ---
# ==========================================

def run_euler_explorer():
    st.title("🌀 Universal Euler Product Explorer")
    st.markdown("Hunt for periodic patterns and partial expansions in arithmetic progressions of $q$-series.")

    with st.sidebar:
        st.header("⚙️ 1. Series Definition")
        st.info("Supports $q^k$ shifts and integer scalars! Example: `2 q f_2`")
        latex_input = st.text_area("Enter LaTeX Formula:", value=r"\frac{f_2^5}{f_1^2 f_3^2}", height=80)
        st.latex(latex_input)
        st.divider()
        
        st.header("🔍 2. Search Parameters")
        max_degree = st.number_input("Max Degree (q-expansion)", min_value=50, max_value=5000, value=200, step=50)
        progression = st.number_input("Base Progression (m)", min_value=2, value=2, step=1)
        offset = st.number_input("Offset (r)", min_value=0, max_value=progression - 1, value=0, step=1)
        run_btn = st.button("🚀 Calculate Exponents", type="primary", use_container_width=True)

    if run_btn:
        start_time = time.time()
        def f(n): return QSeries(generate_base_pochhammer(n, max_degree), max_degree)
        q_obj = QSeries([0, 1] + [0]*max_degree, max_degree)
        safe_env = {"f": f, "q": q_obj, "__builtins__": {}}
        python_formula = latex_to_python(latex_input)

        try:
            with st.spinner(f"Expanding series up to O(q^{max_degree}) and calculating exact Moebius inversions..."):
                final_series = eval(python_formula, safe_env)
                if not isinstance(final_series, QSeries):
                    final_series = QSeries([int(final_series)] + [0]*max_degree, max_degree)
                G_coeffs = final_series.coeffs
                
                H_coeffs_raw = [G_coeffs[i] for i in range(offset, max_degree + 1, progression)]
                if not H_coeffs_raw: st.error("The max degree is too low to extract this progression."); st.stop()

                first_term = H_coeffs_raw[0]
                if first_term == 0: st.error(f"The first term of this progression ({progression}n + {offset}) is 0. It cannot be converted to a standard Euler product."); st.stop()
                    
                H_coeffs = [Fraction(int(c), int(first_term)) for c in H_coeffs_raw]
                a_exponents = compute_euler_exponents(H_coeffs, len(H_coeffs) - 1)
                
                df = pd.DataFrame({"n": range(1, len(a_exponents)), "a(n)": a_exponents[1:]})
                calc_time = time.time() - start_time
                st.success(f"Calculated exact exponents for the **{progression}n + {offset}** progression! (Normalized by a factor of {first_term}) in {calc_time:.2f}s")
                
                is_clean = all(isinstance(val, int) or val.is_integer() for val in a_exponents[1:])
                if not is_clean: st.warning("⚠️ **Note:** The resulting exponents contain decimals. This progression does not factor cleanly into an infinite product of integers.")
                
                col1, col2 = st.columns([1, 2])
                with col1: st.dataframe(df, use_container_width=True, hide_index=True)
                with col2: st.line_chart(df.set_index("n"))

                if is_clean:
                    seq = a_exponents[1:]
                    seq_len = len(seq)
                    best_stride, best_coverage, best_components = 1, 0, {}
                    for stride in range(1, 13):
                        components, covered_indices = {}, 0
                        for r in range(1, stride + 1):
                            sub_seq = [seq[i] for i in range(r - 1, seq_len, stride)]
                            if len(sub_seq) < 3: components[r] = {"is_periodic": False}; continue
                            detected_p = None
                            for p in range(1, min(20, len(sub_seq) // 3 + 1)):
                                is_p = True
                                for i in range(len(sub_seq)):
                                    if abs(sub_seq[i] - sub_seq[i % p]) > 1e-4: is_p = False; break
                                if is_p: detected_p = p; break
                            if detected_p is not None:
                                components[r] = {"is_periodic": True, "p": detected_p, "pattern": [int(x) for x in sub_seq[:detected_p]]}
                                covered_indices += len(sub_seq)
                            else: components[r] = {"is_periodic": False}
                        if covered_indices > best_coverage:
                            best_coverage, best_stride, best_components = covered_indices, stride, components
                        if covered_indices == seq_len: break

                    if best_coverage > 0:
                        st.divider()
                        if best_coverage == seq_len:
                            st.subheader("🎯 Exact Product Expression Discovered!")
                            st.info(f"The Euler exponents are perfectly periodic. (Analyzed using grouping stride $m={best_stride}$)")
                        else:
                            st.subheader("🧩 Partial Product Expression Discovered!")
                            st.warning(f"The sequence is **MIXED**. Some sub-progressions are beautifully periodic, while others are wild. (Analyzed using grouping stride $m={best_stride}$)")
                            
                        num_str, den_str, unknown_r = [], [], []
                        for r in range(1, best_stride + 1):
                            comp = best_components[r]
                            if comp["is_periodic"]:
                                p, pattern = comp["p"], comp["pattern"]
                                st.write(f"**Terms $n \equiv {r} \pmod{{{best_stride}}}$:** Repeats `{pattern}`")
                                for j in range(p):
                                    a_val = pattern[j]
                                    if a_val == 0: continue
                                    base_power, step_power = r + j * best_stride, best_stride * p
                                    r_str = "q" if base_power == 1 else f"q^{{{base_power}}}"
                                    P_str = "q" if step_power == 1 else f"q^{{{step_power}}}"
                                    term = rf"({r_str}; {P_str})_\infty"
                                    if a_val < 0:
                                        if abs(a_val) == 1: num_str.append(term)
                                        else: num_str.append(term + rf"^{{{abs(a_val)}}}")
                                    elif a_val > 0:
                                        if a_val == 1: den_str.append(term)
                                        else: den_str.append(term + rf"^{{{a_val}}}")
                            else:
                                unknown_r.append(r)
                                st.write(f"**Terms $n \equiv {r} \pmod{{{best_stride}}}$:** Non-periodic/Wild")
                                
                        num_final = " ".join(num_str) if num_str else "1"
                        den_final = " ".join(den_str) if den_str else "1"
                        unknown_str = r" \times F_{\text{unknown}}(q)" if unknown_r else ""
                            
                        if den_final == "1": final_latex = rf"H(q) = {num_final}{unknown_str}"
                        elif num_final == "1": final_latex = rf"H(q) = \frac{{1}}{{{den_final}}}{unknown_str}"
                        else: final_latex = rf"H(q) = \frac{{{num_final}}}{{{den_final}}}{unknown_str}"
                            
                        st.success("### Extracted Product Equation")
                        st.latex(final_latex)
                        st.code(final_latex, language="latex")
                        if unknown_r:
                            un_list = ", ".join(map(str, unknown_r))
                            st.markdown(f"*Note: $F_{{\\text{{unknown}}}}(q)$ absorbs all the wild, non-periodic terms for $n \equiv {un_list} \pmod{{{best_stride}}}$.*")

        except Exception as e: st.error(f"Failed to evaluate expression: {e}")

# ==========================================
# --- MODULE 3: ETA-MULTIPLIER PRO ---
# ==========================================

def run_eta_multiplier():
    st.title("🛡️ Modular Form Eta-Multiplier Finder")
    st.markdown("Search for eta-quotient multipliers to force holomorphicity at cusps.")

    with st.sidebar:
        st.header("⚙️ 1. Base Quotient Definition")
        latex_input = st.text_area("Enter LaTeX Formula:", value=r"\frac{1}{f_1 f_2^{36}}", height=80)
        st.latex(latex_input)
        st.divider()

        st.header("⚙️ 2. Configuration")
        col_t, col_r, col_N = st.columns(3)
        t = col_t.number_input("Modulo (t)", value=43)
        r = col_r.number_input("Rem (r)", value=12)
        N = col_N.number_input("Level (N)", value=4)
        
        st.divider()
        search_mode = st.radio("Mode", ["Standard (All Divisors)", "Deep Search (Targeted)"], label_visibility="collapsed")
        target_k, targeted_divs = None, []
        if search_mode == "Standard (All Divisors)":
            k_mode = st.radio("Optimization", ["Auto (Minimal k, allows negatives)", "Strict (Target k, positive only)"])
            if k_mode == "Strict (Target k, positive only)":
                target_k = st.number_input("Target k", value=12)
                min_e, max_e = 0, st.number_input("Max Exponent Bound", value=10)
            else:
                col1, col2 = st.columns(2)
                with col1: min_e = st.number_input("Min Exponent", value=-2)
                with col2: max_e = st.number_input("Max Exponent", value=10)
        else:
            all_divs = get_divisors(N)
            targeted_divs = st.multiselect("Select Divisors for Multiplier", all_divs, default=[1])
            col1, col2 = st.columns(2)
            with col1: min_e = st.number_input("Min Exponent", value=0)
            with col2: max_e = st.number_input("Max Exponent", value=1000)

        st.divider()
        stop_mode = st.radio("Search Limit", ["Find All Valid Multipliers", "Stop After Finding N Results"])
        limit_n, limit_sturm = None, None
        if stop_mode == "Stop After Finding N Results":
            col3, col4 = st.columns(2)
            with col3: limit_n = st.number_input("Stop after N:", value=10, min_value=1)
            with col4: limit_sturm = st.number_input("Max Sturm:", value=250, min_value=1)

        run_btn = st.button("🔍 Run Analysis", type="primary", use_container_width=True)

    if run_btn:
        try:
            def f_dict(n): return EtaDictTerm({n: 1})
            safe_env = {"f": f_dict, "__builtins__": {}}
            python_formula = latex_to_python(latex_input)
            
            try: base_obj = eval(python_formula, safe_env)
            except NameError as e:
                if 'q' in str(e) or 'X' in str(e):
                    st.error("❌ **Invalid Input:** The Eta-Multiplier calculates formal modular weights and cusps, which requires pure eta-quotients. Parameters like `X` or shifts like `q^k` are exclusively for the Miner and Euler Explorer.")
                else: st.error(f"❌ **Variable Error:** `{e}`")
                st.stop()
            except Exception as e: 
                st.error(f"❌ **Invalid Input:** Requires pure eta-quotients. Details: {e}"); st.stop()

            if not isinstance(base_obj, EtaDictTerm): st.error("Please enter a valid eta-quotient."); st.stop()
            base_dict = base_obj.terms

            with st.spinner("Crunching the numbers... Please wait."):
                res = find_eta_multipliers(t, r, N, tuple(base_dict.items()), min_e, max_e, search_mode, target_k, tuple(targeted_divs), limit_n, limit_sturm)
            
            if not res: st.error("❌ No valid multipliers exist for these parameters.")
            else:
                st.success(f"Found {len(res)} candidates.")
                for idx, item in enumerate(res):
                    with st.expander(f"Candidate {idx+1} | Total Weight k = {item['k']} | Sturm = {item['sturm']}", expanded=(idx==0)):
                        tab1, tab2 = st.tabs(["📊 Visual Dashboard", "📝 Copy LaTeX Export"])
                        with tab1:
                            col1, col2 = st.columns([1, 1.2])
                            with col1:
                                mult_lat = "".join([f"\\eta^{{{v}}}({k}z)" if v not in [0, 1] else (f"\\eta({k}z)" if v == 1 else "") for k, v in item['multiplier'].items() if v != 0])
                                st.latex(f"M(z) = {mult_lat or '1'}")
                                st.metric("Total Shift (b)", item['total_b'])
                            with col2:
                                md_table = "| Cusp ($1/d$) | Vanishing Order |\n| :---: | :---: |\n"
                                for c, val in item['cusp_orders'].items(): md_table += f"| $1/{c}$ | ${format_latex_frac(val)}$ |\n"
                                st.markdown(md_table)
                        with tab2:
                            st.code(generate_latex_export(t, r, N, base_dict, item), language="latex")

        except Exception as e: st.error(f"Analysis failed. Details: {e}")

# ==========================================
# --- MODULE 4: DISSECTION DICTIONARY ---
# ==========================================

def get_sym_env():
    def f(n): return SymExpr([SymTerm(1, 0, {int(n): 1})])
    q_obj = SymExpr([SymTerm(1, 1, {})])
    return {"f": f, "q": q_obj, "X": 1, "__builtins__": {}}

def load_dissections():
    return [
        {"type": "2-dissection", "name": "f_1^2", "nice_name": "f₁²", "latex_lhs": "f_1^2", "latex_rhs": r"\frac{f_2 f_8^5}{f_4^2 f_{16}^2} - 2q\frac{f_2 f_{16}^2}{f_8}"},
        {"type": "2-dissection", "name": "1/f_1^2", "nice_name": "1 / f₁²", "latex_lhs": r"\frac{1}{f_1^2}", "latex_rhs": r"\frac{f_8^5}{f_2^5 f_{16}^2} + 2q\frac{f_4^2 f_{16}^2}{f_2^5 f_8}"},
        {"type": "2-dissection", "name": "f_1^4", "nice_name": "f₁⁴", "latex_lhs": r"f_1^4", "latex_rhs": r"\frac{f_4^{10}}{f_2^2 f_8^4} - 4q\frac{f_2^2 f_8^4}{f_4^2}"},
        {"type": "2-dissection", "name": "1/f_1^4", "nice_name": "1 / f₁⁴", "latex_lhs": r"\frac{1}{f_1^4}", "latex_rhs": r"\frac{f_4^{14}}{f_2^{14} f_8^4} + 4q\frac{f_4^2 f_8^4}{f_2^{10}}"},
        {"type": "2-dissection", "name": "f_1 f_3", "nice_name": "f₁ f₃", "latex_lhs": r"f_1 f_3", "latex_rhs": r"\frac{f_2 f_8^2 f_{12}^4}{f_4^2 f_6 f_{24}^2} - q\frac{f_4^4 f_6 f_{24}^2}{f_2 f_8^2 f_{12}^2}"},
        {"type": "2-dissection", "name": "1/(f_1 f_3)", "nice_name": "1 / (f₁ f₃)", "latex_lhs": r"\frac{1}{f_1 f_3}", "latex_rhs": r"\frac{f_8^2 f_{12}^5}{f_2^2 f_4 f_6^4 f_{24}^2} + q\frac{f_4^5 f_{24}^2}{f_2^4 f_6^2 f_8^2 f_{12}}"},
        {"type": "2-dissection", "name": "f_3/f_1^3", "nice_name": "f₃ / f₁³", "latex_lhs": r"\frac{f_3}{f_1^3}", "latex_rhs": r"\frac{f_4^6 f_6^3}{f_2^9 f_{12}^2} + 3q\frac{f_4^2 f_6 f_{12}^2}{f_2^7}"},
        {"type": "2-dissection", "name": "f_3^3/f_1", "nice_name": "f₃³ / f₁", "latex_lhs": r"\frac{f_3^3}{f_1}", "latex_rhs": r"\frac{f_4^3 f_6^2}{f_2^2 f_{12}} + q\frac{f_{12}^3}{f_4}"},
        {"type": "2-dissection", "name": "f_1/f_3", "nice_name": "f₁ / f₃", "latex_lhs": r"\frac{f_1}{f_3}", "latex_rhs": r"\frac{f_2 f_{16} f_{24}^2}{f_6^2 f_8 f_{48}} - q\frac{f_2 f_8^2 f_{12} f_{48}}{f_4 f_6^2 f_{16} f_{24}}"},
        {"type": "2-dissection", "name": "f_3/f_1", "nice_name": "f₃ / f₁", "latex_lhs": r"\frac{f_3}{f_1}", "latex_rhs": r"\frac{f_4 f_6 f_{16} f_{24}^2}{f_2^2 f_8 f_{12} f_{48}} + q\frac{f_6 f_8^2 f_{48}}{f_2^2 f_{16} f_{24}}"},
        {"type": "2-dissection", "name": "f_1^2/f_3^2", "nice_name": "f₁² / f₃²", "latex_lhs": r"\frac{f_1^2}{f_3^2}", "latex_rhs": r"\frac{f_2 f_4^2 f_{12}^4}{f_6^5 f_8 f_{24}} - 2q\frac{f_2^2 f_8 f_{12} f_{24}}{f_4 f_6^4}"},
        {"type": "2-dissection", "name": "f_1/f_5", "nice_name": "f₁ / f₅", "latex_lhs": r"\frac{f_1}{f_5}", "latex_rhs": r"\frac{f_2 f_8 f_{20}^3}{f_4 f_{10}^3 f_{40}} - q\frac{f_4^2 f_{40}}{f_8 f_{10}^2}"},
        {"type": "2-dissection", "name": "f_5/f_1", "nice_name": "f₅ / f₁", "latex_lhs": r"\frac{f_5}{f_1}", "latex_rhs": r"\frac{f_8 f_{20}^2}{f_2^2 f_{40}} + q\frac{f_4^3 f_{10} f_{40}}{f_2^3 f_8 f_{20}}"},

        {"type": "3-dissection", "name": "f_1^2/f_2", "nice_name": "f₁² / f₂", "latex_lhs": r"\frac{f_1^2}{f_2}", "latex_rhs": r"\frac{f_9^2}{f_{18}} - 2q\frac{f_3 f_{18}^2}{f_6 f_9}"},
        {"type": "3-dissection", "name": "f_2/f_1^2", "nice_name": "f₂ / f₁²", "latex_lhs": r"\frac{f_2}{f_1^2}", "latex_rhs": r"\frac{f_6^4 f_9^6}{f_3^8 f_{18}^3} + 2q\frac{f_6^3 f_9^3}{f_3^7} + 4q^2\frac{f_6^2 f_{18}^3}{f_3^6}"},
        {"type": "3-dissection", "name": "f_1 f_4/f_2", "nice_name": "(f₁ f₄) / f₂", "latex_lhs": r"\frac{f_1 f_4}{f_2}", "latex_rhs": r"\frac{f_3 f_{12} f_{18}^5}{f_6^2 f_9^2 f_{36}^2} - q\frac{f_9 f_{36}}{f_{18}}"},
        {"type": "3-dissection", "name": "f_2/(f_1 f_4)", "nice_name": "f₂ / (f₁ f₄)", "latex_lhs": r"\frac{f_2}{f_1 f_4}", "latex_rhs": r"\frac{f_{18}^9}{f_3^2 f_9^3 f_{12}^2 f_{36}^3} + q\frac{f_6^2 f_{18}^3}{f_3^3 f_{12}^3} + q^2\frac{f_6^4 f_9^3 f_{36}^3}{f_3^4 f_{12}^4 f_{18}^3}"},
        {"type": "3-dissection", "name": "f_1^3", "nice_name": "f₁³", "latex_lhs": r"f_1^3", "latex_rhs": r"\frac{f_6 f_9^6}{f_3 f_{18}^3} - 3q f_9^3 + 4q^3\frac{f_3^2 f_{18}^6}{f_6^2 f_9^3}"},
        {"type": "3-dissection", "name": "f_1 f_2", "nice_name": "f₁ f₂", "latex_lhs": r"f_1 f_2", "latex_rhs": r"\frac{f_6 f_9^4}{f_3 f_{18}^2} - q f_9 f_{18} - 2q^2\frac{f_3 f_{18}^4}{f_6 f_9^2}"}
    ]

def run_dissection_dictionary():
    st.title("📚 Algebraic Dissection Dictionary")
    st.markdown("Database of modular dissections with built-in symbolic manipulation and $q$-substitution engine.")
    
    db = load_dissections()
    types = ["All"] + sorted(list(set(item["type"] for item in db)))
    
    st.write("### 1. Filter by Dissection Type")
    selected_type = st.radio("Choose a category to view all related dissections at once:", types, horizontal=True)
    st.write("---")
    
    if selected_type == "All": filtered_db = db
    else:
        filtered_db = [item for item in db if item["type"] == selected_type]
        st.write(f"### Showing all {selected_type}s")
        for item in filtered_db: st.latex(f"{item['latex_lhs']} = {item['latex_rhs']}")
        st.write("---")
        
    st.write("### 2. Symbolic Math Sandbox")
    selected_func = st.selectbox(
        "Select a base identity to manipulate:", 
        options=[""] + filtered_db, 
        format_func=lambda x: x["nice_name"] if isinstance(x, dict) else x
    )
    
    if selected_func and isinstance(selected_func, dict):
        target = selected_func
        st.write("#### Base Identity:")
        st.latex(f"{target['latex_lhs']} = {target['latex_rhs']}")
        
        st.divider()
        st.subheader("🛠️ Algebraic Modifier")
        st.info("Apply mathematical transformations. Scale the index (e.g. $q \\to q^3$), expand binomials, and cancel eta-quotients.")
        
        col1, col2, col3, col4 = st.columns(4)
        power_input = col1.number_input("Raise to Power:", value=1, min_value=1, step=1)
        q_scale = col2.number_input("Scale $q \\to q^m$:", value=1, min_value=1, step=1)
        mod_p = col3.number_input("Simplify Mod $p$ (0=Off):", value=0, min_value=0, step=1)
        mult_input = col4.text_input("Multiply by (LaTeX):", value="1", help="E.g., q^2 f_4^3 / f_2")
        
        if st.button("Apply Transformation", type="primary", use_container_width=True):
            try:
                env = get_sym_env()
                base_expr = eval(latex_to_python(target["latex_rhs"]), env).substitute_q(q_scale)
                mult_expr = eval(latex_to_python(mult_input), env)
                
                result_expr = (base_expr ** power_input) * mult_expr
                
                scaled_lhs_str = scale_latex_lhs(target['latex_lhs'], q_scale)
                lhs_mult = mult_input if mult_input.strip() != "1" else ""
                
                if power_input == 1:
                    lhs = f"{scaled_lhs_str} \\times {lhs_mult}" if lhs_mult else scaled_lhs_str
                else:
                    lhs = f"\\left({scaled_lhs_str}\\right)^{{{power_input}}} \\times {lhs_mult}" if lhs_mult else f"\\left({scaled_lhs_str}\\right)^{{{power_input}}}"
                    
                st.success("### Exact Algebraic Expansion")
                st.latex(f"{lhs} = {result_expr.to_latex()}")
                st.code(f"{lhs} = {result_expr.to_latex()}", language="latex")
                
                if mod_p >= 2:
                    mod_expr = result_expr.simplify_mod(mod_p)
                    st.warning(f"### Simplified Modulo {mod_p}")
                    st.latex(f"{lhs} \\equiv {mod_expr.to_latex()} \\pmod{{{mod_p}}}")

            except NameError as e:
                st.error(f"❌ **Variable Error:** `{e}`. Ensure you use standard 'f_n' notation.")
            except SyntaxError as e:
                st.error(f"❌ **Syntax Error:** `{e}`. Check your multiplier formula.")
            except Exception as e:
                st.error(f"❌ **Algebraic evaluation failed:** {e}")

    st.write("---")
    st.write("### 3. Multiply Multiple Dissections")
    st.info("Combine standard dissections, scale them, and multiply by your own custom functions.")
    
    col_db, col_cust, col_mod = st.columns([1, 1.5, 1])
    num_factors = col_db.number_input("Number of Database Factors:", min_value=0, max_value=10, value=2)
    custom_mult = col_cust.text_input("Custom Multiplier (LaTeX):", value="1", help="E.g., q^2 f_4^3 / f_2")
    mod_p_multi = col_mod.number_input("Simplify Mod $p$ (0=Off):", value=0, min_value=0, step=1, key="mod_p_multi")

    selected_factors = []
    
    if num_factors > 0:
        cols = st.columns(min(num_factors, 4)) 
        for i in range(num_factors):
            col = cols[i % len(cols)]
            with col:
                factor = st.selectbox(f"Database Factor {i+1}", options=db, format_func=lambda x: x["nice_name"], key=f"multi_factor_{i}")
                scale = st.number_input(f"Scale $q \\to q^m$ (Slot {i+1})", value=1, min_value=1, key=f"scale_{i}")
                selected_factors.append((factor, scale))

    if st.button("Calculate Final Product", type="primary", use_container_width=True):
        try:
            env = get_sym_env()
            
            combined_expr = eval(latex_to_python(custom_mult), env)
            lhs_parts = []

            for target, scale in selected_factors:
                expr = eval(latex_to_python(target["latex_rhs"]), env).substitute_q(scale)
                scaled_lhs = scale_latex_lhs(target['latex_lhs'], scale)
                lhs_parts.append(f"\\left({scaled_lhs}\\right)")
                
                combined_expr = combined_expr * expr

            if custom_mult.strip() != "1":
                lhs_parts.insert(0, custom_mult.strip())

            if not lhs_parts:
                lhs_combined = "1"
            else:
                lhs_combined = " \\times ".join(lhs_parts)
                
            st.success("### Combined Expansion Result")
            st.latex(f"{lhs_combined} = {combined_expr.to_latex()}")
            st.code(f"{lhs_combined} = {combined_expr.to_latex()}", language="latex")
            
            if mod_p_multi >= 2:
                mod_expr = combined_expr.simplify_mod(mod_p_multi)
                st.warning(f"### Simplified Modulo {mod_p_multi}")
                st.latex(f"{lhs_combined} \\equiv {mod_expr.to_latex()} \\pmod{{{mod_p_multi}}}")
                
        except NameError as e:
            st.error(f"❌ **Variable Error:** `{e}`. Ensure you use standard 'f_n' notation.")
        except SyntaxError as e:
            st.error(f"❌ **Syntax Error:** `{e}`. Check your multiplier formula.")
        except Exception as e:
            st.error(f"❌ **Failed to combine dissections:** {e}")

# ==========================================
# --- MODULE 5: DISSECTION STRATEGIST ---
# ==========================================

def run_strategy_suggestor():
    st.title("🧠 Algebraic Dissection Strategist")
    st.markdown("Analyze an eta-quotient and receive a step-by-step mathematical guide for manual algebraic dissection.")

    with st.sidebar:
        st.header("⚙️ 1. Series Definition")
        st.info("Input a pure eta-quotient using standard LaTeX (e.g., `\\frac{f_8}{f_1 f_3 f_4}`).")
        latex_input = st.text_area("Enter LaTeX Formula:", value=r"\frac{f_8}{f_1 f_3 f_4}", height=80)
        st.latex(latex_input)
        st.divider()

        st.header("🔍 2. Target Dissection")
        modulo = st.number_input("Modulo (p-dissection)", min_value=2, value=3, step=1)
        run_btn = st.button("🚀 Analyze Strategy", type="primary", use_container_width=True)

    if run_btn:
        try:
            def f_dict(n): return EtaDictTerm({n: 1})
            safe_env = {"f": f_dict, "__builtins__": {}}
            python_formula = latex_to_python(latex_input)
            
            try: base_obj = eval(python_formula, safe_env)
            except Exception: st.error("❌ **Invalid Input:** Please provide a pure product/quotient."); st.stop()

            if not isinstance(base_obj, EtaDictTerm): st.error("Please enter a valid eta-quotient."); st.stop()

            base_dict = base_obj.terms
            nums, dens = [], []
            for d, p in base_dict.items():
                if p > 0: nums.extend([d] * p)
                elif p < 0: dens.extend([d] * abs(p))
            all_bases = nums + dens

            st.subheader(f"Strategy Report for {modulo}-Dissection")
            st.markdown("---")
            
            step_counter, found_known = 1, False
            constants_num = list(set([b for b in nums if b % modulo == 0]))
            constants_den = list(set([b for b in dens if b % modulo == 0]))
            
            if constants_num or constants_den:
                constants_str = ", ".join([f"$f_{{{b}}}$" for b in constants_num + constants_den])
                st.info(f"**Step {step_counter}: Isolate Constants**\n\nIsolate {constants_str}. Since their subscripts are exact multiples of {modulo}, they act as constants when extracting the $q^{{{modulo}n}}$ terms. Pull them out of the summation first.")
                step_counter += 1

            if modulo == 2:
                if 1 in dens and 3 in dens: st.success(f"**Step {step_counter}: Standard Substitution**\n\nApply the standard 2-dissection for $1/(f_1 f_3)$ discovered by Hirschhorn."); found_known = True
                if 1 in nums and 5 in nums: st.success(f"**Step {step_counter}: Standard Substitution**\n\nApply the standard 2-dissection for $f_1 f_5$ (Hirschhorn)."); found_known = True
                if 1 in dens and 5 in dens: st.success(f"**Step {step_counter}: Standard Substitution**\n\nApply the standard 2-dissection for $1/(f_1 f_5)$."); found_known = True
            elif modulo == 3:
                if 1 in dens and 3 in dens: st.success(f"**Step {step_counter}: Ramanujan's Cubic Fraction**\n\nGroup $1/(f_1 f_3)$. You can translate this using Ramanujan's cubic continued fraction or convert to theta functions before dissecting."); found_known = True
                if nums.count(1) >= 2 and 2 in dens: st.success(f"**Step {step_counter}: Known Dissection**\n\nIsolate $f_1^2 / f_2$. Apply the known 3-dissection: $\\varphi(-q^3) - 2q(f_3 f_{{18}}^2)/(f_6 f_9)$."); found_known = True
                if nums.count(2) >= 1 and dens.count(1) >= 2: st.success(f"**Step {step_counter}: Known Dissection**\n\nIsolate $f_2 / f_1^2$. Apply its standard 3-dissection (Lemma 3.9)."); found_known = True
                if 1 in dens and not any(x in dens for x in [2,3]): st.success(f"**Step {step_counter}: Standard Substitution**\n\nFor $1/f_1$, use the standard 3-dissection from Hirschhorn involving $f_9^3/f_3^4$ and $f_{{36}}$."); found_known = True
            elif modulo == 5:
                if 1 in dens and not any(x in dens for x in [2,3,4]): st.success(f"**Step {step_counter}: Rogers-Ramanujan**\n\nFor a 5-dissection of $1/f_1$, use the Rogers-Ramanujan continued fraction $R(q)$ expansion (Lemma 4)."); found_known = True
                if nums.count(1) >= 4: st.success(f"**Step {step_counter}: Ramanujan's Master Identity**\n\nYou have $f_1^4$. Use Ramanujan's famous 1919 identity for the 5-dissection to prove $p(5n+4) \\equiv 0 \\pmod 5$."); found_known = True
            elif modulo == 7:
                if nums.count(1) >= 6: st.success(f"**Step {step_counter}: Ramanujan's Master Identity**\n\nYou have $f_1^6$. Use Ramanujan's identity involving $R(q^7)$ to extract the 7-dissection."); found_known = True
                elif 1 in dens: st.success(f"**Step {step_counter}: General p-Dissection**\n\nFor $1/f_1$, apply the general p-dissection formula (Cui & Gu lemma) mapping to theta functions."); found_known = True

            if found_known: step_counter += 1

            if not found_known and len(all_bases) >= 3 and modulo >= 3:
                N = lcm_list(list(set(all_bases)))
                st.warning(f"**Step {step_counter} (Algorithmic Priority): Transition to Modular Forms**\n\nAlgebraic dissection by hand will likely explode in complexity here. Transition to the theory of modular forms:\n* Check if your eta-quotient is a modular form on $\\Gamma_0({N})$.\n* Map the progression to a modular curve and calculate the order of the cusps using Sturm's Bound.\n* If the coefficients are congruent to $0 \\pmod {{{modulo}}}$ up to the Sturm bound, the congruence is proven universally.")
                step_counter += 1

            if not found_known and (len(all_bases) < 3 or modulo < 3):
                st.warning(f"**Step {step_counter}: Manual Expansion**\n\nNo specific grouped dissection found in the internal database. Expand the remaining terms using Euler's Pentagonal Number Theorem or Jacobi's Triple Product, multiply the series, and extract the {modulo}-dissection manually.")

        except Exception as e: st.error(f"Analysis failed. Details: {e}")

# ==========================================
# --- MASTER NAVIGATION CONTROLLER ---
# ==========================================

st.set_page_config(page_title="Ramanujan Laboratory", page_icon="♾️", layout="wide")
# ==========================================
# --- MASTER NAVIGATION CONTROLLER ---
# ==========================================

st.set_page_config(page_title="Ramanujan Laboratory", page_icon="♾️", layout="wide")

# --- CLEAN TOP-RIGHT BRANDING ---
header_left, header_right = st.columns([3, 1])
with header_right:
    st.markdown(
        """
        <div style="text-align: right; color: gray; font-size: 15px; margin-top: -20px;">
            <b>Developed by Pankaj Gogoi</b><br>
            <i>Tezpur University</i>
        </div>
        """,
        unsafe_allow_html=True
    )
st.markdown("---") # Optional: Adds a neat line under your name
# --- END BRANDING ---

st.sidebar.title("🧭 Main Menu")
app_mode = st.sidebar.selectbox("Select Application Module:", ["⛏️ Congruence Miner", "🌀 Euler Product Explorer", "🛡️ Eta-Multiplier Pro", "📚 Dissection Dictionary", "🧠 Dissection Strategist"])
st.sidebar.divider()

if app_mode == "⛏️ Congruence Miner": run_congruence_miner()
elif app_mode == "🌀 Euler Product Explorer": run_euler_explorer()
elif app_mode == "🛡️ Eta-Multiplier Pro": run_eta_multiplier()
elif app_mode == "📚 Dissection Dictionary": run_dissection_dictionary()
elif app_mode == "🧠 Dissection Strategist": run_strategy_suggestor()
