import streamlit as st
import pandas as pd
import time
import re
import math
import os
import pickle
import hashlib
import shutil
from fractions import Fraction
from itertools import product
from functools import reduce

# ==========================================
# --- INITIALIZE APP, BRANDING & STATE ---
# ==========================================
st.set_page_config(page_title="Ramanujan Laboratory", page_icon="♾️", layout="wide")

if "latex_clipboard" not in st.session_state:
    st.session_state.latex_clipboard = []

def add_to_clipboard(source, latex_content):
    if not latex_content.strip().startswith("$$") and not latex_content.strip().startswith("%"):
        latex_content = f"$$\n{latex_content}\n$$"
    entry = f"% --- {source} ---\n{latex_content}"
    if entry not in st.session_state.latex_clipboard:
        st.session_state.latex_clipboard.append(entry)

header_left, header_right = st.columns([3, 1])
with header_right:
    st.markdown(
        """
        <div style="text-align: right; color: gray; font-size: 15px; margin-top: -20px;">
            <b>Developed by Pankaj Gogoi</b><br>
            <i>Tezpur University</i><br>
            <span style="font-size: 11px;">gopankajgo07@gmail.com</span>
        </div>
        """,
        unsafe_allow_html=True
    )
st.markdown("---")

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

def gen_phi(k, limit):
    C = [0] * (limit + 1)
    n = 0
    while n*n*k <= limit:
        C[n*n*k] += 1 if n == 0 else 2
        n += 1
    return QSeries(C, limit)

def gen_psi(k, limit):
    C = [0] * (limit + 1)
    n = 0
    while n*(n+1)//2 * k <= limit:
        C[n*(n+1)//2 * k] += 1
        n += 1
    return QSeries(C, limit)

def gen_fab(a, b, limit):
    C = [0] * (limit + 1)
    n = 0
    while True:
        exp_pos = a*(n*(n+1)//2) + b*(n*(n-1)//2)
        m = -n
        exp_neg = a*(m*(m+1)//2) + b*(m*(m-1)//2)
        added = False
        if exp_pos <= limit:
            C[exp_pos] += 1
            added = True
        if n != 0 and exp_neg <= limit:
            C[exp_neg] += 1
            added = True
        if not added and exp_pos > limit and exp_neg > limit:
            break
        n += 1
    return QSeries(C, limit)

def gen_Psi_ab(a, b, limit):
    C = [0] * (limit + 1)
    
    # Positive n (from 0 to infinity)
    n = 0
    while True:
        exp_pos = a * (n * (n + 1) // 2) + b * (n * (n - 1) // 2)
        if exp_pos <= limit:
            C[exp_pos] += 1
        elif n > 0: 
            break
        n += 1

    # Negative n (from -1 down to -infinity)
    n = -1
    while True:
        exp_neg = a * (n * (n + 1) // 2) + b * (n * (n - 1) // 2)
        if exp_neg <= limit:
            C[exp_neg] -= 1
        else:
            break
        n -= 1
        
    return QSeries(C, limit)

def q_pochhammer_series(k, n, limit):
    res = QSeries([1] + [0]*limit, limit)
    for j in range(1, n + 1):
        if k*j > limit: break
        term = QSeries([1] + [0]*limit, limit)
        term.coeffs[k*j] = -1
        res = res * term
    return res

def gen_G(k, limit):
    res = QSeries([0]*(limit+1), limit)
    n = 0
    while k * n * n <= limit:
        num = QSeries([0]*(limit+1), limit)
        num.coeffs[k*n*n] = 1
        den = q_pochhammer_series(k, n, limit)
        res = res + (num / den)
        n += 1
    return res

def gen_H(k, limit):
    res = QSeries([0]*(limit+1), limit)
    n = 0
    while k * n * (n+1) <= limit:
        num = QSeries([0]*(limit+1), limit)
        num.coeffs[k*n*(n+1)] = 1
        den = q_pochhammer_series(k, n, limit)
        res = res + (num / den)
        n += 1
    return res

def latex_to_python(latex_str):
    s = latex_str.replace('$', '').replace('\r', '').replace('\n', '')
    s = re.sub(r'\\(?:varphi|phi)\s*\(\s*q\^?\{?([0-9X]*)\}?\s*\)', lambda m: f"phi({m.group(1) or '1'})", s)
    s = re.sub(r'\\psi\s*\(\s*q\^?\{?([0-9X]*)\}?\s*\)', lambda m: f"psi({m.group(1) or '1'})", s)
    s = re.sub(r'\\Psi\s*\(\s*q\^?\{?([0-9X]*)\}?\s*,\s*q\^?\{?([0-9X]*)\}?\s*\)', lambda m: f"Psi({m.group(1) or '1'}, {m.group(2) or '1'})", s)
    s = re.sub(r'\\Psi\s*\(\s*([0-9X]+)\s*,\s*([0-9X]+)\s*\)', lambda m: f"Psi({m.group(1)}, {m.group(2)})", s)
    s = re.sub(r'G\s*\(\s*q\^?\{?([0-9X]*)\}?\s*\)', lambda m: f"G({m.group(1) or '1'})", s)
    s = re.sub(r'H\s*\(\s*q\^?\{?([0-9X]*)\}?\s*\)', lambda m: f"H({m.group(1) or '1'})", s)
    s = re.sub(r'f\s*\(\s*q\^?\{?([0-9X]*)\}?\s*,\s*q\^?\{?([0-9X]*)\}?\s*\)', lambda m: f"fab({m.group(1) or '1'}, {m.group(2) or '1'})", s)
    
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
    s = re.sub(r'(\d)\(', r'\1*(', s)
    
    return s

def lcm(a, b): return abs(a*b) // math.gcd(a, b) if a and b else 0
def lcm_list(lst): return reduce(lcm, lst, 1) if lst else 1

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0: return False
    return True

# ==========================================
# --- SMART CACHING ARCHITECTURE ---
# ==========================================
if "smart_ram_cache" not in st.session_state:
    st.session_state.smart_ram_cache = {}

def _core_expansion_engine(latex_str, limit):
    """Core mathematical evaluation logic."""
    def f(n): 
        if int(n) <= 0: return QSeries([1] + [0]*limit, limit)
        return QSeries(generate_base_pochhammer(int(n), limit), limit)
    
    q_obj = QSeries([0, 1] + [0]*limit, limit)
    python_formula = latex_to_python(latex_str)
    
    safe_env = {
        "f": f, "q": q_obj, "X": 1, 
        "phi": lambda k: gen_phi(int(k), limit), 
        "psi": lambda k: gen_psi(int(k), limit), 
        "G": lambda k: gen_G(int(k), limit), 
        "H": lambda k: gen_H(int(k), limit), 
        "fab": lambda a, b: gen_fab(int(a), int(b), limit), 
        "Psi": lambda a, b: gen_Psi_ab(int(a), int(b), limit),
        "__builtins__": {}
    }

    final_series = eval(python_formula, safe_env)
    if not isinstance(final_series, QSeries): 
        final_series = QSeries([int(final_series)] + [0]*limit, limit)
    return final_series.coeffs

def get_smart_expansion(latex_str, limit, persist_to_disk=False):
    """
    Checks if a larger or equal expansion already exists for this exact formula.
    If yes, it instantly slices and returns the subset. 
    If no, it computes the new ceiling and saves it.
    """
    if not persist_to_disk:
        cache = st.session_state.smart_ram_cache
        if latex_str in cache:
            if cache[latex_str]["limit"] >= limit:
                st.toast(f"⚡ Smart Cache Hit: Sliced from {cache[latex_str]['limit']:,} terms in RAM!")
                return cache[latex_str]["coeffs"][:limit + 1]
        
        coeffs = _core_expansion_engine(latex_str, limit)
        st.session_state.smart_ram_cache[latex_str] = {"limit": limit, "coeffs": coeffs}
        return coeffs
    else:
        cache_dir = ".streamlit/smart_cache"
        os.makedirs(cache_dir, exist_ok=True)
        safe_name = hashlib.md5(latex_str.encode()).hexdigest()
        file_path = os.path.join(cache_dir, f"{safe_name}.pkl")
        
        if os.path.exists(file_path):
            with open(file_path, "rb") as f:
                saved_data = pickle.load(f)
            if saved_data["limit"] >= limit:
                st.toast(f"⚡ Smart Cache Hit: Sliced from {saved_data['limit']:,} terms on Disk!")
                return saved_data["coeffs"][:limit + 1]
        
        coeffs = _core_expansion_engine(latex_str, limit)
        with open(file_path, "wb") as f:
            pickle.dump({"limit": limit, "coeffs": coeffs}, f)
        return coeffs

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
        base_etas = {}
        for k, v in self.etas.items():
            curr_k, curr_v = k, v
            while curr_k % p == 0:
                curr_k //= p
                curr_v *= p
            base_etas[curr_k] = base_etas.get(curr_k, 0) + curr_v
        
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
        return SymTerm(self.coeff, self.q_power, new_etas)

    def apply_Up(self, p, r=0):
        if self.q_power % p != r: 
            return None
            
        new_etas = {}
        for k, v in self.etas.items():
            if k % p != 0: 
                raise ValueError(f"Cannot formally apply U_{p} to f_{{{k}}}. All eta subscripts must be multiples of {p}.")
            new_etas[k // p] = v
            
        return SymTerm(self.coeff, (self.q_power - r) // p, new_etas)

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

    def apply_Up(self, p, r=0):
        new_terms = []
        for t in self.terms:
            new_t = t.apply_Up(p, r)
            if new_t is not None: 
                new_terms.append(new_t)
        return SymExpr(new_terms) if new_terms else SymExpr([SymTerm(0)])

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
# --- MODULE 3/5/6 SPECIFIC MATH ENGINE ---
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

def compute_euler_exponents(c_array, max_terms):
    def get_moebius(n):
        if n == 1: return 1
        p = 0
        for i in range(2, int(n**0.5) + 1):
            if n % (i * i) == 0: return 0
            if n % i == 0:
                p += 1
                n //= i
                while n % i == 0: return 0
        if n > 1: p += 1
        return -1 if p % 2 != 0 else 1

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

def format_latex_frac(val):
    if val.denominator == 1: return str(val.numerator)
    return rf"\frac{{{val.numerator}}}{{{val.denominator}}}"

def find_eta_multipliers(t, r, N, base_dict_items, min_e, max_e, search_mode, target_k, targeted_divs, limit_n, limit_sturm):
    base_dict = dict(base_dict_items)
    divs = get_divisors(N) if search_mode == "Standard (All Divisors)" else list(targeted_divs)
    if not divs: return []
    
    results = []
    ranges = [range(min_e, max_e + 1) for _ in divs]
    
    index = N
    temp_n = N
    d = 2
    primes = set()
    while d * d <= temp_n:
        if temp_n % d == 0:
            primes.add(d)
            while temp_n % d == 0: temp_n //= d
        d += 1
    if temp_n > 1: primes.add(temp_n)
    for p in primes:
        index = int(index * (1 + 1/p))

    gcd_cache = {}
    for d_cusp in get_divisors(N):
        for delta in list(set(divs + list(base_dict.keys()))):
            gcd_cache[(d_cusp, delta)] = math.gcd(d_cusp, delta)
            
    for combo in product(*ranges):
        m_dict = {d: e for d, e in zip(divs, combo)}
        total_dict = {k: base_dict.get(k, 0) + m_dict.get(k, 0) for k in set(base_dict) | set(m_dict)}
        
        sum_vals = sum(total_dict.values())
        if sum_vals % 2 != 0: continue
        total_weight = sum_vals // 2
        
        if target_k is not None:
            if total_weight != target_k: continue
        else:
            if total_weight <= 0: continue
            
        sturm = math.ceil((total_weight * index) / 12)
        if limit_sturm is not None and sturm > limit_sturm: continue
        
        is_holo = True
        cusp_orders = {}
        for d_cusp in get_divisors(N):
            s = Fraction(0)
            for delta, val in total_dict.items():
                s += Fraction(gcd_cache[(d_cusp, delta)]**2 * val, delta)
            
            order = s * Fraction(N, 24 * math.gcd(d_cusp**2, N))
            cusp_orders[d_cusp] = order
            
            if order < 0:
                is_holo = False
                break
                
        if not is_holo: continue
        
        total_shift = Fraction(sum(delta * val for delta, val in total_dict.items()), 24)
        
        item = {
            "multiplier": {k: v for k, v in m_dict.items() if v != 0},
            "k": total_weight,
            "sturm": sturm,
            "cusp_orders": cusp_orders,
            "total_b": total_shift
        }
        results.append(item)
        
        if limit_n is not None and len(results) >= limit_n:
            break
            
    return results

def generate_latex_export(t, r, N, base_dict, item):
    mult_lat = " ".join([f"f_{{{k}}}^{{{v}}}" if v not in [0, 1] else (f"f_{{{k}}}" if v == 1 else "") for k, v in item['multiplier'].items() if v != 0])
    if not mult_lat: mult_lat = "1"
    return f"% Multiplier M(z) forcing holomorphicity on \\Gamma_0({N})\n% Total Weight k = {item['k']}, Sturm = {item['sturm']}\n{mult_lat}"

# ==========================================
# --- MODULE 1: INFINITE FAMILY MINER ---
# ==========================================
def run_infinite_family_miner():
    st.title("♾️ Infinite Family Congruence Miner")
    st.markdown("Discover generalized, infinite $q$-series congruences modulo any $p$. Supports complex polynomials via global Symbolic Engine.")

    def ifm_targeted_sieve(coeffs, mod, max_k, bases, min_A0, max_A0, safety_divisor):
        N = len(coeffs)
        hits = set()
        for base in bases:
            for A0 in range(min_A0, max_A0 + 1):
                for k in range(max_k + 1):
                    A = A0 * (base ** k)
                    if A < 2 or A > N / safety_divisor: continue 
                    for B in range(A):
                        sequence = [coeffs[i] for i in range(B, N, A) if i != 0]
                        if len(sequence) >= 5 and all(term % mod == 0 for term in sequence):
                            hits.add((A, B))
                            
        sorted_hits = sorted(list(hits), key=lambda x: x[0])
        fundamental_hits = []
        for A, B in sorted_hits:
            is_trivial = False
            for A_f, B_f in fundamental_hits:
                if A % A_f == 0 and B % A_f == B_f:
                    is_trivial = True
                    break
            if not is_trivial: fundamental_hits.append((A, B))
        return fundamental_hits

    def ifm_detect_infinite_families(hits, mod):
        if len(hits) < 3: return []
        families = []
        for i in range(len(hits) - 2):
            A0, B0 = hits[i]
            for j in range(i + 1, len(hits) - 1):
                A1, B1 = hits[j]
                if A1 % A0 != 0: continue
                R = A1 // A0
                if R <= 1: continue
                num = B1 - B0
                den = R - 1
                c1 = Fraction(num, den)
                c2 = Fraction(B0) - c1
                A2 = A1 * R
                expected_B2 = int(c1 * (R**2) + c2)
                if (A2, expected_B2) in hits:
                    families.append({"A0": A0, "R": R, "c1": c1, "c2": c2, "mod": mod})
        return families

    with st.sidebar:
        st.header("⚙️ 1. Search Limits")
        st.caption("⚠️ *Generating > 50,000 terms takes significant time.*")
        N = st.number_input("Terms to Generate ($N$)", min_value=1000, value=75000, step=1000)
        max_k = st.number_input("Max Search Depth ($k$)", min_value=3, value=8)
        
        st.markdown("### Memory / Caching Strategy")
        cache_mode = st.radio(
            "Save Computations:",
            ["Temporarily (RAM - Clears on exit)", "Permanently (Disk - Survives reboots)"],
            index=0
        )
        
        st.markdown("### Advanced Optimization")
        safety_divisor = st.selectbox(
            "Safety Valve Threshold (N divisor)",
            options=[6.0, 4.8],
            format_func=lambda x: "Strict (N // 6) - Requires massive N" if x == 6.0 else "Optimized (N / 4.8) - Saves computation",
            index=1
        )

        st.markdown("### Base Step Range ($A_0$)")
        col1, col2 = st.columns(2)
        min_A0 = col1.number_input("Min $A_0$", min_value=1, value=1)
        max_A0 = col2.number_input("Max $A_0$", min_value=min_A0, value=30)
        
        st.header("🎯 2. Target Vectors")
        manual_mods = st.text_input("Target Moduli ($p$):", value="5")
        manual_bases = st.text_input("Step Bases ($R$):", value="25")

    st.subheader("1. Define Parametric Series")
    st.info("Powered by the Global Symbolic Engine. Supports additions, subtractions, and special functions like `\\psi(q)`.")
    user_input = st.text_area("Enter Series LaTeX Formula:", value=r"\frac{1}{f_1 f_2^2}")
    st.latex(user_input)
    st.markdown("---")

    if st.button("🚀 Execute Deep Sieve", type="primary", use_container_width=True):
        try:
            test_mods = [int(m.strip()) for m in manual_mods.split(",") if m.strip().isdigit()]
            test_bases = [int(b.strip()) for b in manual_bases.split(",") if b.strip().isdigit()]
            
            if not test_mods or not test_bases:
                st.error("Please enter valid numbers."); st.stop()

            with st.spinner(f"Generating first {N:,} terms algebraically (Smart Cached)..."):
                start_time = time.time()
                if cache_mode.startswith("Temporarily"):
                    coeffs = get_smart_expansion(user_input, N, persist_to_disk=False)
                else:
                    coeffs = get_smart_expansion(user_input, N, persist_to_disk=True)
                
            st.success(f"Series expansion $O(q^{{{N}}})$ ready in {time.time() - start_time:.3f} seconds.")
            
            all_families = []
            all_raw_hits = {}
            
            with st.spinner("Sieving vectors and applying Triviality Filter..."):
                for mod in test_mods:
                    raw_hits = ifm_targeted_sieve(coeffs, mod, max_k, test_bases, min_A0, max_A0, safety_divisor)
                    if raw_hits:
                        all_raw_hits[mod] = raw_hits
                        families = ifm_detect_infinite_families(raw_hits, mod)
                        all_families.extend(families)

            st.subheader("📊 Analysis Results")
            tab1, tab2, tab3 = st.tabs(["✨ Discovered Infinite Families", "🎯 Fundamental Isolated Hits", "🧮 Series Expansion Data"])
            
            with tab1:
                if not all_families:
                    st.warning("No infinite geometric families detected in this search space.")
                else:
                    st.success(f"Discovered {len(all_families)} generalized infinite families!")
                    collected_latex_lines = []
                    
                    for fam in all_families:
                        mod, A0, R, c1, c2 = fam['mod'], fam['A0'], fam['R'], fam['c1'], fam['c2']
                        c1_str = f"\\frac{{{abs(c1.numerator)}}}{{{c1.denominator}}}" if c1.denominator != 1 else str(abs(c1.numerator))
                        c2_str = f"\\frac{{{abs(c2.numerator)}}}{{{c2.denominator}}}" if c2.denominator != 1 else str(abs(c2.numerator))
                        
                        c1_sign = "+" if c1 >= 0 else "-"
                        c2_sign = "+" if c2 >= 0 else "-"
                        
                        display_str = rf"c\left( {A0} \cdot {R}^k \cdot n {c1_sign} {c1_str} \cdot {R}^k {c2_sign} {c2_str} \right) \equiv 0 \pmod {{{mod}}} \quad \forall k \ge 0"
                        aligned_str = rf"c\left( {A0} \cdot {R}^k \cdot n {c1_sign} {c1_str} \cdot {R}^k {c2_sign} {c2_str} \right) &\equiv 0 \pmod {{{mod}}} \quad \forall k \ge 0"
                        
                        st.latex(display_str)
                        collected_latex_lines.append(aligned_str)
                        
                    bulk_latex_string = "\\begin{aligned}\n" + " \\\\\n".join(collected_latex_lines) + "\n\\end{aligned}"
                    add_to_clipboard("Infinite Families Found", bulk_latex_string)
                    st.info("✅ Results automatically sent to the Global LaTeX Clipboard in the sidebar.")
                        
            with tab2:
                if not all_raw_hits: st.warning("No standalone progressions found.")
                else:
                    for mod, hits in all_raw_hits.items():
                        st.markdown(f"### Modulo {mod}")
                        st.dataframe(pd.DataFrame(hits, columns=["A (Step)", "B (Offset)"]), use_container_width=True)
                        
            with tab3:
                st.write(coeffs[:100])

        except SyntaxError as e:
            st.error(f"❌ **Syntax Error:** `{e}`. Ensure you use standard notation.")
        except Exception as e:
            st.error(f"Execution Error. Details: {e}")

# ==========================================
# --- MODULE 2: CONGRUENCE MINER ---
# ==========================================
def run_congruence_miner():
    st.title("⛏️ Absolute $q$-Series Congruence Miner")

    with st.sidebar:
        st.header("⚙️ 1. Series Definition")
        template_cols = st.columns([3, 1])
        with template_cols[0]:
            template = st.selectbox("📖 Insert Special Function:", ["Select a template...", r"\frac{1}{f_1 \psi(q^3)}", r"\varphi(q^2)"])
        with template_cols[1]:
            st.write(""); st.write("")
            if st.button("Inject") and template != "Select a template...":
                st.session_state.miner_latex_input = template
                st.rerun()
                
        if "miner_latex_input" not in st.session_state: st.session_state.miner_latex_input = r"\frac{1}{f_1 \psi(q^3)}"
        latex_input = st.text_area("Enter LaTeX Formula:", value=st.session_state.miner_latex_input, height=80)
        st.latex(latex_input)
        st.divider()

        st.markdown("### 🧮 Inject False Theta $\\Psi(a,b)$")
        col_a, col_b = st.columns(2)
        psi_a = col_a.number_input("Parameter a (power of q)", value=1, min_value=0, key="psi_a")
        psi_b = col_b.number_input("Parameter b (power of q)", value=2, min_value=0, key="psi_b")
        
        if st.button("Inject $\\Psi(q^a, q^b)$"):
            st.session_state.miner_latex_input = rf"\Psi(q^{{{psi_a}}}, q^{{{psi_b}}})"
            st.rerun()
            
        st.divider()
        
        st.header("🔍 2. Analysis Mode")
        mode = st.radio("Select Tool:", [
            "Single Pattern Check", 
            "Full Progression Sweep", 
            "Hunter Mode (Run until found)", 
            "Parametric Family Search",
            "Prime Sieve Sweep (Primes ≤ n)"
        ])
        st.divider()
        
        if mode == "Single Pattern Check":
            col_k, col_r, col_M = st.columns(3)
            A_val, B_val, M_val = col_k.number_input("k", value=5), col_r.number_input("r", value=4), col_M.number_input("M", value=5)
        elif mode == "Full Progression Sweep":
            col_k, col_M = st.columns(2)
            sweep_k, sweep_M = col_k.number_input("Stride (k)", value=5), col_M.number_input("Modulus (M)", value=5)
        elif mode == "Prime Sieve Sweep (Primes ≤ n)":
            col_p, col_k = st.columns(2)
            max_p = col_p.number_input("Max Prime (n)", value=13, min_value=2)
            hunt_max = col_k.number_input("Max k to search", value=50)
        elif mode == "Parametric Family Search":
            col_min, col_max = st.columns(2)
            x_min, x_max = col_min.number_input("X Start", value=1), col_max.number_input("X End", value=5)
            hunt_M, hunt_max = st.number_input("Modulus", value=5), st.number_input("Stop k", value=20)
        else:
            hunt_M = st.number_input("Modulus", value=5)
            hunt_strategy = st.radio("Strategy:", ["Stop at First", "Collect Multiple"])
            hunt_bounty_limit = st.number_input("Max Bounties", value=10) if hunt_strategy == "Collect Multiple" else 1 
            hunt_max = st.number_input("Stop k", value=100)
            
        st.divider()
        limit = st.number_input("Terms to compute (N)", value=3000, step=100)
        
        st.markdown("### Memory / Caching")
        cache_mode = st.radio("Save Computations:", ["Temporarily (RAM)", "Permanently (Disk)"], key="miner_cache")
        run_btn = st.button("🚀 Run Miner", type="primary", use_container_width=True)

    if run_btn:
        try:
            if cache_mode.startswith("Temporarily"):
                F_q = get_smart_expansion(latex_input, limit, persist_to_disk=False)
            else:
                F_q = get_smart_expansion(latex_input, limit, persist_to_disk=True)

            if mode == "Parametric Family Search":
                def build_env(x_val=1):
                    q_obj = QSeries([0, 1] + [0]*limit, limit)
                    def f(n): 
                        if int(n) <= 0: return QSeries([1] + [0]*limit, limit)
                        return QSeries(generate_base_pochhammer(int(n), limit), limit)
                    return {"f": f, "q": q_obj, "X": x_val, "phi": lambda k: gen_phi(int(k), limit), "psi": lambda k: gen_psi(int(k), limit), "G": lambda k: gen_G(int(k), limit), "H": lambda k: gen_H(int(k), limit), "fab": lambda a, b: gen_fab(int(a), int(b), limit), "Psi": lambda a, b: gen_Psi_ab(int(a), int(b), limit), "__builtins__": {}}
                
                family_results = []
                python_formula = latex_to_python(latex_input)
                with st.spinner("Scanning..."):
                    for x_val in range(int(x_min), int(x_max) + 1):
                        try:
                            final_series = eval(python_formula, build_env(x_val))
                            if not isinstance(final_series, QSeries): final_series = QSeries([int(final_series)] + [0]*limit, limit)
                            F_q_param = final_series.coeffs
                            found_for_x = []
                            fundamental_hits = []
                            
                            for current_k in range(2, hunt_max + 1):
                                for r in range(current_k):
                                    max_n = (limit - r) // current_k
                                    if max_n < 5: continue 
                                    
                                    is_trivial = False
                                    for hit_k, hit_r in fundamental_hits:
                                        if current_k % hit_k == 0 and r % hit_k == hit_r:
                                            is_trivial = True; break
                                    if is_trivial: continue
                                    
                                    is_congruent = True
                                    for n_val in range(max_n + 1):
                                        idx = current_k * n_val + r
                                        if idx == 0: continue 
                                        if idx <= limit and F_q_param[idx] % hunt_M != 0:
                                            is_congruent = False; break
                                    if is_congruent: 
                                        fundamental_hits.append((current_k, r))
                                        found_for_x.append(rf"c({current_k}n + {r}) \equiv 0 \pmod{{{hunt_M}}}")
                                        
                            if found_for_x: 
                                family_results.append({"X Value": x_val, f"Congruences mod {hunt_M}": ", ".join(found_for_x)})
                                add_to_clipboard(f"Parametric Congruences (X={x_val})", " \\\\\n".join(found_for_x))
                        except Exception as e: pass
                st.info("✅ Trivial sub-progressions filtered out.")
                st.table(pd.DataFrame(family_results))

            elif mode == "Single Pattern Check":
                success_count, total_checked, failures = 0, 0, []
                max_n = (limit - B_val) // A_val
                for n_val in range(max_n + 1):
                    idx = A_val * n_val + B_val
                    if idx == 0: continue 
                    if idx > limit: break
                    if F_q[idx] % M_val == 0: success_count += 1
                    else: failures.append({"n": n_val})
                if not failures: 
                    st.success("🎉 Verified!")
                    lat_str = rf"c({A_val}n + {B_val}) \equiv 0 \pmod{{{M_val}}}"
                    st.latex(lat_str)
                    add_to_clipboard("Verified Congruence", lat_str)
                    
            elif mode == "Full Progression Sweep":
                found_congruences = []
                fundamental_hits = []
                for r in range(sweep_k):
                    max_n = (limit - r) // sweep_k
                    if max_n < 5: continue 
                    
                    is_congruent = True
                    for n_val in range(max_n + 1):
                        idx = sweep_k * n_val + r
                        if idx == 0: continue 
                        if idx <= limit and F_q[idx] % sweep_M != 0: 
                            is_congruent = False; break
                    if is_congruent: 
                        found_congruences.append((sweep_k, r, max_n + 1))
                        
                if found_congruences:
                    st.success(f"Discovered {len(found_congruences)} valid congruence(s)!")
                    lat_strs = [rf"c({k}n + {r}) \equiv 0 \pmod{{{sweep_M}}}" for k, r, _ in found_congruences]
                    for ls in lat_strs: st.latex(ls)
                    add_to_clipboard("Sweep Congruences", " \\\\\n".join(lat_strs))

            elif mode == "Prime Sieve Sweep (Primes ≤ n)":
                primes = [p for p in range(2, int(max_p) + 1) if is_prime(p)]
                sieve_results = []
                progress_bar = st.progress(0)

                with st.spinner(f"Sieving primes up to {int(max_p)}..."):
                    for idx, p in enumerate(primes):
                        found_for_p = False
                        for current_k in range(2, int(hunt_max) + 1):
                            if found_for_p: break
                            for r in range(current_k):
                                max_n = (limit - r) // current_k
                                if max_n < 5: continue

                                is_congruent = True
                                for n_val in range(max_n + 1):
                                    idx_q = current_k * n_val + r
                                    if idx_q == 0: continue
                                    if idx_q <= limit and F_q[idx_q] % p != 0:
                                        is_congruent = False; break

                                if is_congruent:
                                    res_lat = rf"c({current_k}n + {r}) \equiv 0 \pmod{{{p}}}"
                                    sieve_results.append({"Prime (p)": p, "k": current_k, "r": r, "Congruence": res_lat})
                                    add_to_clipboard(f"Sieve Result Mod {p}", res_lat)
                                    found_for_p = True
                                    break
                        progress_bar.progress((idx + 1) / len(primes))

                if sieve_results:
                    st.success(f"🎯 Discovered congruences for {len(sieve_results)} primes.")
                    for item in sieve_results:
                        st.latex(item["Congruence"])
                    st.dataframe(pd.DataFrame(sieve_results).drop(columns=["Congruence"]), use_container_width=True)
                else:
                    st.warning("No congruences found for these primes within the search limit.")

            else:
                found_matches = []
                for current_k in range(2, hunt_max + 1):
                    for r in range(current_k):
                        max_n = (limit - r) // current_k
                        if max_n < 5: continue 
                        
                        is_trivial = False
                        for hit in found_matches:
                            if current_k % hit['k'] == 0 and r % hit['k'] == hit['r']:
                                is_trivial = True; break
                        if is_trivial: continue
                        
                        is_congruent = True
                        for n_val in range(max_n + 1):
                            idx = current_k * n_val + r
                            if idx == 0: continue 
                            if idx <= limit and F_q[idx] % hunt_M != 0: 
                                is_congruent = False; break
                        if is_congruent:
                            found_matches.append({"k": current_k, "r": r, "terms": max_n + 1})
                            if len(found_matches) >= hunt_bounty_limit: break
                    if len(found_matches) >= hunt_bounty_limit: break
                    
                if found_matches:
                    st.success(f"🎯 Mined {len(found_matches)} congruences. (Trivial subsets ignored)")
                    lat_strs = [rf"c({hit['k']}n + {hit['r']}) \equiv 0 \pmod{{{hunt_M}}}" for hit in found_matches]
                    for ls in lat_strs: st.latex(ls)
                    add_to_clipboard(f"Mined Congruences Mod {hunt_M}", " \\\\\n".join(lat_strs))
                    
        except Exception as e: st.error(f"Failed: {e}")

# ==========================================
# --- MODULE 3: EULER PRODUCT EXPLORER ---
# ==========================================
def run_euler_explorer():
    st.title("🌀 Universal Euler Product Explorer")

    with st.sidebar:
        st.header("⚙️ 1. Series Definition")
        latex_input = st.text_area("Enter LaTeX Formula:", value=r"\frac{f_2^5}{f_1^2 f_3^2}")
        st.header("🔍 2. Search Parameters")
        max_degree = st.number_input("Max Degree (q-expansion)", value=200, step=50)
        progression = st.number_input("Base Progression (m)", value=2)
        offset = st.number_input("Offset (r)", value=0)
        
        st.markdown("### Memory / Caching")
        cache_mode = st.radio("Save Computations:", ["Temporarily (RAM)", "Permanently (Disk)"], key="euler_cache")
        run_btn = st.button("🚀 Calculate Exponents", type="primary", use_container_width=True)

    if run_btn:
        try:
            if cache_mode.startswith("Temporarily"):
                G_coeffs = get_smart_expansion(latex_input, max_degree, persist_to_disk=False)
            else:
                G_coeffs = get_smart_expansion(latex_input, max_degree, persist_to_disk=True)
            
            H_coeffs_raw = [G_coeffs[i] for i in range(offset, max_degree + 1, progression)]
            first_term = H_coeffs_raw[0]
                
            H_coeffs = [Fraction(int(c), int(first_term)) for c in H_coeffs_raw]
            a_exponents = compute_euler_exponents(H_coeffs, len(H_coeffs) - 1)
            
            is_clean = all(isinstance(val, int) or val.is_integer() for val in a_exponents[1:])
            
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
                    num_str, den_str, unknown_r = [], [], []
                    for r in range(1, best_stride + 1):
                        comp = best_components[r]
                        if comp["is_periodic"]:
                            p, pattern = comp["p"], comp["pattern"]
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
                        else: unknown_r.append(r)
                            
                    num_final = " ".join(num_str) if num_str else "1"
                    den_final = " ".join(den_str) if den_str else "1"
                    unknown_str = r" \times F_{\text{unknown}}(q)" if unknown_r else ""
                        
                    if den_final == "1": final_latex = rf"\sum c({progression}n+{offset})q^n = {num_final}{unknown_str}"
                    elif num_final == "1": final_latex = rf"\sum c({progression}n+{offset})q^n = \frac{{1}}{{{den_final}}}{unknown_str}"
                    else: final_latex = rf"\sum c({progression}n+{offset})q^n = \frac{{{num_final}}}{{{den_final}}}{unknown_str}"
                        
                    st.success("### Extracted Product Equation")
                    st.latex(final_latex)
                    add_to_clipboard(f"Euler Product ({progression}n+{offset})", final_latex)
                    
        except Exception as e: st.error(f"Failed to evaluate expression: {e}")

# ==========================================
# --- MODULE 4: ETA-MULTIPLIER PRO ---
# ==========================================
def run_eta_multiplier():
    st.title("🛡️ Modular Form Eta-Multiplier Finder")

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
                min_e = 0
                max_e = st.number_input("Max Exponent Bound", value=10)
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
            except Exception as e: 
                st.error(f"❌ **Invalid Input:** Requires pure eta-quotients. Details: {e}"); st.stop()

            if not isinstance(base_obj, EtaDictTerm): st.error("Please enter a valid eta-quotient."); st.stop()
            base_dict = base_obj.terms

            with st.spinner("Crunching the holomorphicity bounds..."):
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
                                st.metric("Total Shift (b)", str(item['total_b']))
                            with col2:
                                md_table = "| Cusp ($1/d$) | Vanishing Order |\n| :---: | :---: |\n"
                                for c, val in item['cusp_orders'].items(): md_table += f"| $1/{c}$ | ${format_latex_frac(val)}$ |\n"
                                st.markdown(md_table)
                        with tab2:
                            export_code = generate_latex_export(t, r, N, base_dict, item)
                            st.code(export_code, language="latex")
                            if st.button(f"Push to Global Clipboard (Candidate {idx+1})", key=f"btn_push_{idx}"):
                                add_to_clipboard(f"Eta Multiplier M(z) for Level {N}", export_code)
                                st.toast("Added to clipboard!")

        except Exception as e: st.error(f"Analysis failed. Details: {e}")

# ==========================================
# --- MODULE 5: DISSECTION DICTIONARY ---
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
        st.info("Apply mathematical transformations. Scale the index (e.g. $q \\to q^m$), expand binomials, and cancel eta-quotients.")
        
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
                add_to_clipboard("Algebraic Expansion", f"{lhs} &= {result_expr.to_latex()}")
                
                if mod_p >= 2:
                    mod_expr = result_expr.simplify_mod(mod_p)
                    st.warning(f"### Simplified Modulo {mod_p}")
                    st.latex(f"{lhs} \\equiv {mod_expr.to_latex()} \\pmod{{{mod_p}}}")
                    add_to_clipboard(f"Modulo {mod_p} Reduction", f"{lhs} &\\equiv {mod_expr.to_latex()} \\pmod{{{mod_p}}}")

            except Exception as e:
                st.error(f"❌ **Algebraic evaluation failed:** {e}")

    st.write("---")
    st.write("### 3. Multiply Multiple Dissections")
    st.info("Combine standard dissections, scale them, and multiply by your own custom functions.")
    
    col_db, col_cust, col_mod = st.columns([1, 1.5, 1])
    num_factors = col_db.number_input("Number of Database Factors:", min_value=0, max_value=10, value=2)
    custom_mult = col_cust.text_input("Custom Multiplier (LaTeX):", value="1", help="E.g., q^2 f_4^3 / f_2", key="cm_mult")
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

    st.write("---")
    st.write("### ⚡ Apply $U_p$ Operator")
    st.info("Extracts terms where the $q$-power is $\\equiv r \\pmod p$, then scales the generating function $q \\to q^{1/p}$.")
    
    col_up_check, col_up_p, col_up_r = st.columns([1, 1, 1])
    apply_up = col_up_check.checkbox("Enable $U_p$ Operator")
    up_p = col_up_p.number_input("Prime/Modulo (p):", value=2, min_value=2, step=1, disabled=not apply_up)
    up_r = col_up_r.number_input("Extract Remainder (r):", value=0, min_value=0, step=1, disabled=not apply_up)

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
            add_to_clipboard("Combined Expansion", f"{lhs_combined} &= {combined_expr.to_latex()}")
            
            # --- U_p Operator Logic ---
            if apply_up:
                try:
                    up_expr = combined_expr.apply_Up(up_p, up_r)
                    st.success(f"### Result after $U_{{{up_p}}}$ Operator (extracted $q^{{{up_r}}}$)")
                    
                    lat_lhs_up = f"U_{{{up_p}}}\\left( q^{{{-up_r}}} \\left( {lhs_combined} \\right) \\right)" if up_r > 0 else f"U_{{{up_p}}}\\left( {lhs_combined} \\right)"
                    st.latex(f"{lat_lhs_up} = {up_expr.to_latex()}")
                    add_to_clipboard(f"U_{up_p} Operator", f"{lat_lhs_up} &= {up_expr.to_latex()}")
                    
                    # Update combined_expr for further modulo reduction if chained
                    combined_expr = up_expr
                    lhs_combined = lat_lhs_up
                except ValueError as ve:
                    st.error(f"❌ **U-Operator Error:** {ve}")
            
            # --- Modulo Reduction Logic ---
            if mod_p_multi >= 2:
                mod_expr = combined_expr.simplify_mod(mod_p_multi)
                st.warning(f"### Simplified Modulo {mod_p_multi}")
                st.latex(f"{lhs_combined} \\equiv {mod_expr.to_latex()} \\pmod{{{mod_p_multi}}}")
                add_to_clipboard(f"Combined Modulo {mod_p_multi} Reduction", f"{lhs_combined} &\\equiv {mod_expr.to_latex()} \\pmod{{{mod_p_multi}}}")
                
        except Exception as e:
            st.error(f"❌ **Failed to combine dissections:** {e}")

# ==========================================
# --- MODULE 6: DISSECTION STRATEGIST ---
# ==========================================
def run_strategy_suggestor():
    st.title("🧠 Algebraic Dissection Strategist")

    with st.sidebar:
        st.header("⚙️ 1. Series Definition")
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
            except Exception: st.error("❌ **Invalid Input**"); st.stop()

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
                st.info(f"**Step {step_counter}: Isolate Constants**\n\nIsolate {constants_str}. Since their subscripts are exact multiples of {modulo}, they act as constants.")
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
                if nums.count(1) >= 4: st.success(f"**Step {step_counter}: Ramanujan's Master Identity**\n\nYou have $f_1^4$. Use Ramanujan's famous 1919 identity for the 5-dissection."); found_known = True

            if found_known: step_counter += 1

            if not found_known and len(all_bases) >= 3 and modulo >= 3:
                N_val = lcm_list(list(set(all_bases)))
                st.warning(f"**Step {step_counter} (Algorithmic Priority): Transition to Modular Forms**\n\nAlgebraic dissection by hand will likely explode in complexity here. Transition to the theory of modular forms on $\\Gamma_0({N_val})$.")
                step_counter += 1

            if not found_known and (len(all_bases) < 3 or modulo < 3):
                st.warning(f"**Step {step_counter}: Manual Expansion**\n\nNo specific grouped dissection found in the internal database. Expand the remaining terms manually.")

        except Exception as e: st.error(f"Analysis failed. Details: {e}")

# ==========================================
# --- MASTER NAVIGATION CONTROLLER ---
# ==========================================
st.sidebar.title("🧭 Main Menu")
app_mode = st.sidebar.selectbox("Select Application Module:", [
    "⛏️ Congruence Miner", 
    "♾️ Infinite Family Miner", 
    "🌀 Euler Product Explorer",
    "🛡️ Eta-Multiplier Pro", 
    "📚 Dissection Dictionary",
    "🧠 Dissection Strategist"
])

# --- GLOBAL CLIPBOARD & CACHE UI ---
st.sidebar.markdown("---")
st.sidebar.subheader("📋 System Controls")

col_clip, col_cache = st.sidebar.columns(2)
with col_clip:
    if st.button("🗑️ Clear Clipboard"):
        st.session_state.latex_clipboard = []
        st.rerun()
        
with col_cache:
    if st.button("🧹 Clear All Cache"):
        # 1. Clear the RAM dictionary
        st.session_state.smart_ram_cache = {}
        # 2. Delete the Disk directory
        cache_dir = ".streamlit/smart_cache"
        if os.path.exists(cache_dir):
            shutil.rmtree(cache_dir)
        # 3. Clear Streamlit's native cache just in case
        st.cache_data.clear()
        
        st.success("Cache completely wiped!")
        time.sleep(1)
        st.rerun()

st.sidebar.divider()

if st.session_state.latex_clipboard:
    combined_latex = "\n\n".join(st.session_state.latex_clipboard)
    st.sidebar.info("Click the copy icon in the top right of the code block below.")
    st.sidebar.code(combined_latex, language="latex")
else:
    st.sidebar.info("Clipboard is empty. Run any analysis to collect results here.")

st.sidebar.divider()

if app_mode == "⛏️ Congruence Miner": run_congruence_miner()
elif app_mode == "♾️ Infinite Family Miner": run_infinite_family_miner()
elif app_mode == "🌀 Euler Product Explorer": run_euler_explorer()
elif app_mode == "🛡️ Eta-Multiplier Pro": run_eta_multiplier()
elif app_mode == "📚 Dissection Dictionary": run_dissection_dictionary()
elif app_mode == "🧠 Dissection Strategist": run_strategy_suggestor()
