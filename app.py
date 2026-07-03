import streamlit as st
import ast
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
st.set_page_config(page_title="Ramanujan Laboratory Pro", page_icon="∞", layout="wide")

st.markdown(
    """
    <style>
      .stApp {
        background:
          radial-gradient(circle at 8% 4%, rgba(91, 124, 250, .13), transparent 28%),
          radial-gradient(circle at 92% 7%, rgba(156, 86, 255, .11), transparent 26%);
      }
      .ram-hero {
        padding: 1.25rem 1.45rem;
        border-radius: 20px;
        border: 1px solid rgba(130, 140, 180, .25);
        background: linear-gradient(120deg, rgba(28,35,62,.94), rgba(53,32,88,.91));
        box-shadow: 0 16px 42px rgba(20, 24, 50, .22);
        margin-bottom: 1rem;
      }
      .ram-hero h1 { margin: 0; color: #ffffff; font-size: 2.05rem; }
      .ram-hero p { margin: .35rem 0 0; color: #d9ddff; font-size: 1rem; }
      .ram-card {
        border: 1px solid rgba(128, 139, 180, .22);
        border-radius: 16px;
        padding: .9rem 1rem;
        background: rgba(255,255,255,.035);
      }
      div[data-testid="stMetric"] {
        border: 1px solid rgba(128, 139, 180, .20);
        border-radius: 14px;
        padding: .55rem .75rem;
        background: rgba(255,255,255,.025);
      }
      div[data-testid="stCodeBlock"] { border-radius: 14px; }
      .small-note { opacity: .76; font-size: .88rem; }
    </style>
    <div class="ram-hero">
      <h1>∞ Ramanujan Laboratory Pro</h1>
      <p>Audited eta-quotients, verified dissections, composite q-series analysis, and residue extraction.</p>
    </div>
    """,
    unsafe_allow_html=True,
)

if "latex_clipboard" not in st.session_state:
    st.session_state.latex_clipboard = []


def add_to_clipboard(source, latex_content):
    if not latex_content.strip().startswith("$$") and not latex_content.strip().startswith("%"):
        latex_content = f"$$\n{latex_content}\n$$"
    entry = f"% --- {source} ---\n{latex_content}"
    if entry not in st.session_state.latex_clipboard:
        st.session_state.latex_clipboard.append(entry)


def safe_widget_key(value):
    return re.sub(r"[^A-Za-z0-9_-]+", "_", str(value)).strip("_")[:120] or "latex"


def latex_document(title, body):
    return (
        "\\documentclass[11pt]{article}\n"
        "\\usepackage{amsmath,amssymb}\n"
        "\\usepackage[margin=1in]{geometry}\n"
        "\\newcommand{\\f}[1]{f_{#1}}\n"
        "\\begin{document}\n"
        f"\\section*{{{title}}}\n"
        f"{body}\n"
        "\\end{document}\n"
    )


def render_latex_export(title, latex_code, key, filename=None, add_global=True):
    """Show copyable LaTeX and optional clipboard/download controls."""
    st.markdown(f"**{title}**")
    st.code(latex_code, language="latex")
    cols = st.columns(2 if add_global else 1)
    if add_global:
        with cols[0]:
            if st.button("Add to global LaTeX clipboard", key=f"clip_{safe_widget_key(key)}", use_container_width=True):
                add_to_clipboard(title, latex_code)
                st.toast("LaTeX added to the global clipboard.")
        download_col = cols[1]
    else:
        download_col = cols[0]
    with download_col:
        st.download_button(
            "Download .tex snippet",
            data=latex_code,
            file_name=filename or f"{safe_widget_key(key).lower()}.tex",
            mime="text/x-tex",
            key=f"download_{safe_widget_key(key)}",
            use_container_width=True,
        )


# ==========================================
# --- SHARED MATH ENGINE & PARSER ---
# ==========================================
class QSeries:
    """Truncated formal power series with exact rational coefficients."""

    def __init__(self, coeffs, limit):
        self.limit = int(limit)
        self.coeffs = [self._exact(c) for c in list(coeffs)[: self.limit + 1]]
        if len(self.coeffs) < self.limit + 1:
            self.coeffs += [Fraction(0)] * (self.limit + 1 - len(self.coeffs))

    @staticmethod
    def _exact(value):
        if isinstance(value, Fraction):
            return value
        if isinstance(value, int):
            return Fraction(value)
        if isinstance(value, float):
            return Fraction(str(value))
        return Fraction(value)

    @classmethod
    def one(cls, limit):
        return cls([1], limit)

    @classmethod
    def zero(cls, limit):
        return cls([0], limit)

    def _coerce(self, other):
        if isinstance(other, QSeries):
            if other.limit != self.limit:
                return QSeries(other.coeffs, self.limit)
            return other
        return QSeries([self._exact(other)], self.limit)

    def __neg__(self):
        return QSeries([-c for c in self.coeffs], self.limit)

    def __add__(self, other):
        other = self._coerce(other)
        return QSeries([a + b for a, b in zip(self.coeffs, other.coeffs)], self.limit)

    def __radd__(self, other):
        return self.__add__(other)

    def __sub__(self, other):
        return self.__add__(-self._coerce(other))

    def __rsub__(self, other):
        return self._coerce(other).__sub__(self)

    def __mul__(self, other):
        if not isinstance(other, QSeries):
            scalar = self._exact(other)
            return QSeries([scalar * c for c in self.coeffs], self.limit)
        C = [Fraction(0)] * (self.limit + 1)
        A_nz = [(i, a) for i, a in enumerate(self.coeffs) if a]
        B_nz = [(j, b) for j, b in enumerate(other.coeffs) if b]
        for i, a in A_nz:
            for j, b in B_nz:
                if i + j > self.limit:
                    break
                C[i + j] += a * b
        return QSeries(C, self.limit)

    def __rmul__(self, other):
        return self.__mul__(other)

    def inv(self):
        a0 = self.coeffs[0]
        if a0 == 0:
            raise ZeroDivisionError("A formal power series is invertible only when its constant term is nonzero.")
        B = [Fraction(0)] * (self.limit + 1)
        B[0] = 1 / a0
        for n in range(1, self.limit + 1):
            B[n] = -sum(self.coeffs[k] * B[n-k] for k in range(1, n + 1)) / a0
        return QSeries(B, self.limit)

    def __pow__(self, power):
        if not isinstance(power, int):
            raise TypeError("Formal-series powers must be integers.")
        if power < 0:
            return self.inv() ** (-power)
        result = QSeries.one(self.limit)
        base = self
        exponent = power
        while exponent:
            if exponent & 1:
                result = result * base
            exponent >>= 1
            if exponent:
                base = base * base
        return result

    def __truediv__(self, other):
        if isinstance(other, QSeries):
            return self * other.inv()
        scalar = self._exact(other)
        if scalar == 0:
            raise ZeroDivisionError("division by zero")
        return self * (1 / scalar)

    def __rtruediv__(self, other):
        return self.inv() * other

    def integral_coefficients(self):
        return all(c.denominator == 1 for c in self.coeffs)

    def as_python_numbers(self):
        return [int(c) if c.denominator == 1 else c for c in self.coeffs]

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

def gen_R(k, limit):
    """R(q^k)=(q^k,q^{4k};q^{5k})_infty/(q^{2k},q^{3k};q^{5k})_infty."""
    k = int(k)
    if k <= 0:
        raise ValueError("R(q^k) requires k >= 1.")
    res = QSeries.one(limit)
    step = 5 * k
    n = 0
    while True:
        exponents = [k + n*step, 4*k + n*step, 2*k + n*step, 3*k + n*step]
        if min(exponents) > limit:
            break
        for idx, exponent in enumerate(exponents):
            if exponent > limit:
                continue
            term = QSeries.one(limit)
            term.coeffs[exponent] = -1
            res = res * term if idx < 2 else res / term
        n += 1
    return res

def latex_to_python(latex_str):
    """Convert the supported LaTeX subset to a restricted Python expression."""
    s = latex_str.replace('$', '').replace('\\,', '').replace('\r', '').replace('\n', '')
    function_patterns = [
        (r'\\(?:varphi|phi)\s*\(\s*q\^?\{?([0-9X]*)\}?\s*\)', 'phi'),
        (r'\\psi\s*\(\s*q\^?\{?([0-9X]*)\}?\s*\)', 'psi'),
        (r'G\s*\(\s*q\^?\{?([0-9X]*)\}?\s*\)', 'G'),
        (r'H\s*\(\s*q\^?\{?([0-9X]*)\}?\s*\)', 'H'),
        (r'R\s*\(\s*q\^?\{?([0-9X]*)\}?\s*\)', 'R'),
    ]
    for pattern, name in function_patterns:
        s = re.sub(pattern, lambda m, nm=name: f"{nm}({m.group(1) or '1'})", s)
    s = re.sub(r'\\Psi\s*\(\s*q\^?\{?([0-9X]*)\}?\s*,\s*q\^?\{?([0-9X]*)\}?\s*\)',
               lambda m: f"Psi({m.group(1) or '1'},{m.group(2) or '1'})", s)
    s = re.sub(r'\\Psi\s*\(\s*([0-9X]+)\s*,\s*([0-9X]+)\s*\)',
               lambda m: f"Psi({m.group(1)},{m.group(2)})", s)
    s = re.sub(r'f\s*\(\s*q\^?\{?([0-9X]*)\}?\s*,\s*q\^?\{?([0-9X]*)\}?\s*\)',
               lambda m: f"fab({m.group(1) or '1'},{m.group(2) or '1'})", s)

    def get_group(text, start_i):
        if start_i >= len(text):
            raise SyntaxError("Incomplete \\frac expression.")
        if text[start_i] != '{':
            return text[start_i], start_i + 1
        depth, i = 1, start_i + 1
        while depth and i < len(text):
            depth += (text[i] == '{') - (text[i] == '}')
            i += 1
        if depth:
            raise SyntaxError("Unbalanced braces in \\frac expression.")
        return text[start_i + 1:i - 1], i

    while r'\frac' in s:
        start = s.rfind(r'\frac')  # innermost-first makes nested fractions reliable
        idx = start + 5
        numerator, after_num = get_group(s, idx)
        denominator, after_den = get_group(s, after_num)
        s = s[:start] + f"(({numerator})/({denominator}))" + s[after_den:]

    s = re.sub(r'f_\{([^}]+)\}', r'f(\1)', s)
    s = re.sub(r'f_(\d+|[a-zA-Z])', r'f(\1)', s)
    s = s.replace(r'\left', '').replace(r'\right', '')
    s = s.replace(r'\cdot', '*').replace(r'\times', '*')
    s = s.replace('^', '**').replace('{', '(').replace('}', ')')
    s = s.replace(' ', '').replace('x', 'X')

    # Supported implicit multiplication.
    s = re.sub(r'\)(?=[A-Za-z0-9(])', r')*', s)
    s = re.sub(r'(?<=[0-9qX])(?=[A-Za-z(])', '*', s)
    s = re.sub(r'(?<=q)(?=[0-9])', '*', s)
    return s

def validate_python_formula(expression, allowed_names):
    """Reject attributes, comprehensions, indexing, lambdas, and unapproved calls before eval."""
    tree = ast.parse(expression, mode="eval")
    allowed_nodes = (
        ast.Expression, ast.BinOp, ast.UnaryOp, ast.Call, ast.Name, ast.Load,
        ast.Constant, ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Pow,
        ast.UAdd, ast.USub,
    )
    for node in ast.walk(tree):
        if not isinstance(node, allowed_nodes):
            raise SyntaxError(f"Unsupported or unsafe syntax: {type(node).__name__}.")
        if isinstance(node, ast.Name) and node.id not in allowed_names:
            raise NameError(f"Unsupported symbol '{node.id}'.")
        if isinstance(node, ast.Call):
            if not isinstance(node.func, ast.Name) or node.func.id not in allowed_names:
                raise SyntaxError("Only approved q-series functions may be called.")
            if node.keywords:
                raise SyntaxError("Keyword arguments are not supported.")
    return tree

def restricted_eval(expression, environment):
    validate_python_formula(expression, set(environment) - {"__builtins__"})
    return eval(compile(ast.parse(expression, mode="eval"), "<q-series>", "eval"), environment)

def require_integral_coefficients(coeffs, context="this calculation"):
    output = []
    for n, coefficient in enumerate(coeffs):
        exact = coefficient if isinstance(coefficient, Fraction) else Fraction(coefficient)
        if exact.denominator != 1:
            raise ValueError(
                f"{context} requires integral coefficients, but the coefficient of q^{n} is {exact}."
            )
        output.append(exact.numerator)
    return output

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
        "R": lambda k: gen_R(int(k), limit),
        "fab": lambda a, b: gen_fab(int(a), int(b), limit), 
        "Psi": lambda a, b: gen_Psi_ab(int(a), int(b), limit),
        "__builtins__": {}
    }

    final_series = restricted_eval(python_formula, safe_env)
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
    def __init__(self, coeff=1, q_power=0, etas=None, specials=None):
        self.coeff = Fraction(coeff)
        self.q_power = int(q_power)
        self.etas = {int(k): int(v) for k, v in (etas or {}).items() if v}
        self.specials = {(str(name), int(k)): int(v) for (name, k), v in (specials or {}).items() if v}

    def key(self):
        return (self.q_power, frozenset(self.etas.items()), frozenset(self.specials.items()))

    def substitute_q(self, m):
        m = int(m)
        return SymTerm(
            self.coeff,
            self.q_power * m,
            {k*m: v for k, v in self.etas.items()},
            {(name, k*m): v for (name, k), v in self.specials.items()},
        )

    def simplify_mod(self, p):
        """Use f_k^p == f_{pk} (mod p), including negative exponents."""
        p = int(p)
        if p < 2:
            return self
        final = {}
        for k, exponent in self.etas.items():
            current_k, current_e = k, exponent
            while current_e:
                # Quotient truncated toward zero makes negative exponents terminate:
                # -6 = 5(-1) + (-1), hence f_k^-6 == f_k^-1 f_{5k}^-1 (mod 5).
                quotient = (abs(current_e) // p) * (1 if current_e > 0 else -1)
                remainder = current_e - p * quotient
                if remainder:
                    final[current_k] = final.get(current_k, 0) + remainder
                current_k *= p
                current_e = quotient
        return SymTerm(self.coeff, self.q_power, final, self.specials)

    def apply_Up(self, p, r=0):
        if self.q_power % p != r:
            return None
        if any(k % p for k in self.etas):
            raise ValueError(f"A displayed term contains f_k with p not dividing k; it is not visibly a q^{p}-series.")
        if any(k % p for (_, k) in self.specials):
            raise ValueError(f"A displayed special factor is not visibly a q^{p}-series.")
        return SymTerm(
            self.coeff,
            (self.q_power-r)//p,
            {k//p: v for k, v in self.etas.items()},
            {(name, k//p): v for (name, k), v in self.specials.items()},
        )

    def __mul__(self, other):
        if isinstance(other, (int, float, Fraction)):
            return SymTerm(self.coeff * Fraction(other), self.q_power, self.etas, self.specials)
        etas = self.etas.copy()
        for k, v in other.etas.items():
            etas[k] = etas.get(k, 0) + v
        specials = self.specials.copy()
        for key, v in other.specials.items():
            specials[key] = specials.get(key, 0) + v
        return SymTerm(self.coeff*other.coeff, self.q_power+other.q_power, etas, specials)

    __rmul__ = __mul__

    def __truediv__(self, other):
        if isinstance(other, (int, float, Fraction)):
            return SymTerm(self.coeff/Fraction(other), self.q_power, self.etas, self.specials)
        return self * SymTerm(1/other.coeff, -other.q_power,
                              {k: -v for k, v in other.etas.items()},
                              {key: -v for key, v in other.specials.items()})

    def __rtruediv__(self, other):
        return SymTerm(other) / self

    def __pow__(self, power):
        if not isinstance(power, int):
            raise ValueError("Symbolic powers must be integers.")
        return SymTerm(self.coeff**power, self.q_power*power,
                       {k: v*power for k, v in self.etas.items()},
                       {key: v*power for key, v in self.specials.items()})

    @staticmethod
    def _factor_latex(name, k):
        qarg = "q" if k == 1 else f"q^{{{k}}}"
        return f"{name}({qarg})"

    def to_latex(self):
        if self.coeff == 0:
            return ""
        sign = "+" if self.coeff > 0 else "-"
        abs_c = abs(self.coeff)
        numerator, denominator = [], []
        if self.q_power:
            numerator.append("q" if self.q_power == 1 else f"q^{{{self.q_power}}}")
        for d in sorted(self.etas):
            exponent = self.etas[d]
            factor = f"f_{{{d}}}" + (f"^{{{abs(exponent)}}}" if abs(exponent) != 1 else "")
            (numerator if exponent > 0 else denominator).append(factor)
        for (name, k), exponent in sorted(self.specials.items()):
            factor = self._factor_latex(name, k) + (f"^{{{abs(exponent)}}}" if abs(exponent) != 1 else "")
            (numerator if exponent > 0 else denominator).append(factor)
        if abs_c != 1 or (not numerator and not denominator):
            coefficient = str(abs_c.numerator) if abs_c.denominator == 1 else rf"\frac{{{abs_c.numerator}}}{{{abs_c.denominator}}}"
            numerator.insert(0, coefficient)
        top = " ".join(numerator) or "1"
        bottom = " ".join(denominator)
        return sign + (rf"\frac{{{top}}}{{{bottom}}}" if bottom else top)


class SymExpr:
    def __init__(self, terms):
        self.terms = [terms] if isinstance(terms, SymTerm) else list(terms)
        self.simplify()

    def simplify(self):
        grouped = {}
        for term in self.terms:
            key = term.key()
            if key not in grouped:
                grouped[key] = SymTerm(0, term.q_power, term.etas, term.specials)
            grouped[key].coeff += term.coeff
        self.terms = [t for t in grouped.values() if t.coeff]
        self.terms.sort(key=lambda t: (t.q_power, len(t.etas)+len(t.specials), sorted(t.etas.items())))

    def substitute_q(self, m):
        return SymExpr([t.substitute_q(m) for t in self.terms])

    def simplify_mod(self, p):
        return SymExpr([t.simplify_mod(p) for t in self.terms])

    def apply_Up(self, p, r=0):
        terms = [u for t in self.terms if (u := t.apply_Up(p, r)) is not None]
        return SymExpr(terms or [SymTerm(0)])

    def components(self, p):
        result = {}
        for r in range(p):
            terms = [u for t in self.terms if (u := t.apply_Up(p, r)) is not None]
            result[r] = SymExpr(terms or [SymTerm(0)])
        return result

    def __add__(self, other):
        if isinstance(other, SymExpr):
            return SymExpr(self.terms + other.terms)
        if isinstance(other, SymTerm):
            return SymExpr(self.terms + [other])
        return SymExpr(self.terms + [SymTerm(other)])

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-1)*other

    def __rsub__(self, other):
        return other + (-1)*self

    def __mul__(self, other):
        if isinstance(other, (int, float, Fraction, SymTerm)):
            return SymExpr([t*other for t in self.terms])
        return SymExpr([a*b for a in self.terms for b in other.terms])

    __rmul__ = __mul__

    def __truediv__(self, other):
        if isinstance(other, (int, float, Fraction, SymTerm)):
            return SymExpr([t/other for t in self.terms])
        if isinstance(other, SymExpr) and len(other.terms) == 1:
            return self / other.terms[0]
        raise ValueError("Division by a multi-term symbolic expression is not a finite dissection.")

    def __rtruediv__(self, other):
        if len(self.terms) != 1:
            raise ValueError("Division by a sum is not supported in exact symbolic mode.")
        return SymExpr([other/self.terms[0]])

    def __pow__(self, power):
        if not isinstance(power, int) or power < 0:
            raise ValueError("A finite symbolic dissection can only be raised to a non-negative integer power.")
        result = SymExpr([SymTerm(1)])
        base, exponent = self, power
        while exponent:
            if exponent & 1:
                result = result*base
            exponent >>= 1
            if exponent:
                base = base*base
        return result

    def to_latex(self):
        if not self.terms:
            return "0"
        out = ""
        for i, term in enumerate(self.terms):
            text = term.to_latex()
            if i == 0:
                out += text[1:] if text.startswith('+') else text
            elif text.startswith('-'):
                out += " - " + text[1:]
            else:
                out += " + " + text[1:]
        return out or "0"

    @property
    def term_count(self):
        return len(self.terms)


def scale_latex_lhs(s, m):
    if m == 1:
        return s
    s = re.sub(r'f_\{(\d+)\}', lambda x: f"f_{{{int(x.group(1))*m}}}", s)
    return re.sub(r'f_(\d+)', lambda x: f"f_{{{int(x.group(1))*m}}}", s)

# ==========================================
# --- ETA-QUOTIENT ANALYSIS ENGINE ---
# ==========================================
class EtaDictTerm:
    def __init__(self, terms=None, scalar=1):
        self.terms = {int(d): int(e) for d, e in (terms or {}).items() if e}
        self.scalar = Fraction(scalar)

    def __mul__(self, other):
        if isinstance(other, (int, Fraction)):
            return EtaDictTerm(self.terms, self.scalar*other)
        terms = self.terms.copy()
        for d, e in other.terms.items():
            terms[d] = terms.get(d, 0) + e
        return EtaDictTerm(terms, self.scalar*other.scalar)

    __rmul__ = __mul__

    def __truediv__(self, other):
        if isinstance(other, (int, Fraction)):
            return EtaDictTerm(self.terms, self.scalar/other)
        terms = self.terms.copy()
        for d, e in other.terms.items():
            terms[d] = terms.get(d, 0) - e
        return EtaDictTerm(terms, self.scalar/other.scalar)

    def __rtruediv__(self, other):
        return EtaDictTerm({d: -e for d, e in self.terms.items()}, Fraction(other, 1)/self.scalar)

    def __pow__(self, power):
        if not isinstance(power, int):
            raise ValueError("Eta-product exponents must be integers.")
        return EtaDictTerm({d: e*power for d, e in self.terms.items()}, self.scalar**power)

    @staticmethod
    def _reject_additive_input():
        raise ValueError(
            "This eta-multiplier field accepts one product/quotient only. "
            "For sums or differences, use the Automatic p-Dissection Solver or the Composite Dissection Lab."
        )

    def __add__(self, other):
        self._reject_additive_input()

    __radd__ = __add__

    def __sub__(self, other):
        self._reject_additive_input()

    def __rsub__(self, other):
        self._reject_additive_input()


def parse_eta_product(latex_input):
    def f_dict(n):
        n = int(n)
        if n <= 0:
            raise ValueError("Every f-subscript must be positive.")
        return EtaDictTerm({n: 1})
    obj = restricted_eval(latex_to_python(latex_input), {"f": f_dict, "__builtins__": {}})
    if isinstance(obj, (int, Fraction)):
        obj = EtaDictTerm({}, obj)
    if not isinstance(obj, EtaDictTerm):
        raise ValueError("This module accepts a pure product/quotient of f_d factors.")
    if obj.scalar != 1:
        raise ValueError("Remove scalar constants; they do not affect eta modularity.")
    return obj.terms


def get_divisors(n):
    return [d for d in range(1, int(n)+1) if n % d == 0]


def prime_factorization(n):
    n = abs(int(n))
    factors = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def gamma0_index(N):
    value = Fraction(N)
    for p in prime_factorization(N):
        value *= Fraction(p+1, p)
    return int(value)


def eta_product_latex(exponents, symbol="eta"):
    numerator, denominator = [], []
    for d in sorted(exponents):
        e = exponents[d]
        if not e:
            continue
        if symbol == "eta":
            base = rf"\eta({d}z)" if d != 1 else r"\eta(z)"
        else:
            base = f"f_{{{d}}}"
        factor = base if abs(e) == 1 else base + f"^{{{abs(e)}}}"
        (numerator if e > 0 else denominator).append(factor)
    top = " ".join(numerator) or "1"
    bottom = " ".join(denominator)
    return rf"\frac{{{top}}}{{{bottom}}}" if bottom else top


def squarefree_character_kernel(exponents, weight):
    parity = {}
    for delta, exponent in exponents.items():
        for p, valuation in prime_factorization(delta).items():
            parity[p] = (parity.get(p, 0) + exponent*valuation) % 2
    D = -1 if int(weight) % 2 else 1
    for p, bit in parity.items():
        if bit:
            D *= p
    return D


def analyze_eta_quotient(exponents, N):
    N = int(N)
    if N <= 0:
        raise ValueError("Level N must be positive.")
    bad = [d for d in exponents if N % d]
    if bad:
        raise ValueError(f"The proposed level {N} is not divisible by subscripts {bad}.")
    weight = Fraction(sum(exponents.values()), 2)
    sum_T = sum(delta*e for delta, e in exponents.items())
    sum_S = sum((N//delta)*e for delta, e in exponents.items())
    integral_weight = weight.denominator == 1
    newman_T = sum_T % 24 == 0
    newman_S = sum_S % 24 == 0
    orders = {}
    for c in get_divisors(N):
        order = Fraction(N, 24*math.gcd(c*c, N)) * sum(
            Fraction(math.gcd(c, delta)**2 * e, delta)
            for delta, e in exponents.items()
        )
        orders[c] = order
    holomorphic = all(order >= 0 for order in orders.values())
    cuspidal = all(order > 0 for order in orders.values())
    modular = integral_weight and newman_T and newman_S
    index = gamma0_index(N)
    sturm = math.floor(Fraction(int(weight)*index, 12)) if modular and holomorphic and weight >= 0 else None
    q_shift = Fraction(sum_T, 24)
    character_D = squarefree_character_kernel(exponents, weight) if integral_weight else None
    return {
        "N": N, "weight": weight, "sum_T": sum_T, "sum_S": sum_S,
        "newman_T": newman_T, "newman_S": newman_S,
        "integral_weight": integral_weight, "orders": orders,
        "holomorphic": holomorphic, "cuspidal": cuspidal,
        "modular": modular, "index": index, "sturm": sturm,
        "q_shift": q_shift, "character_D": character_D,
    }


def compute_euler_exponents(c_array, max_terms):
    def mobius(n):
        if n == 1:
            return 1
        factors = prime_factorization(n)
        if sum(factors.values()) != len(factors):
            return 0
        return -1 if len(factors) % 2 else 1
    W = [Fraction(0)]*(max_terms+1)
    for m in range(1, max_terms+1):
        W[m] = m*c_array[m] - sum(W[k]*c_array[m-k] for k in range(1, m))
    a = [Fraction(0)]*(max_terms+1)
    for n in range(1, max_terms+1):
        a[n] = sum(mobius(n//d)*W[d] for d in get_divisors(n))/n
    return [int(x) if x.denominator == 1 else x for x in a]


def format_latex_frac(value):
    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else rf"\frac{{{value.numerator}}}{{{value.denominator}}}"


def find_eta_multipliers(N, base_dict_items, min_e, max_e, target_k=None,
                         targeted_divs=None, limit_n=20, limit_sturm=None,
                         max_combinations=250000):
    base = dict(base_dict_items)
    divisors = list(targeted_divs) if targeted_divs else get_divisors(N)
    if not divisors:
        return [], 0, False
    theoretical = (max_e-min_e+1)**len(divisors)
    checked = 0
    truncated = theoretical > max_combinations
    results = []
    for combo in product(range(min_e, max_e+1), repeat=len(divisors)):
        checked += 1
        if checked > max_combinations:
            break
        multiplier = {d: e for d, e in zip(divisors, combo) if e}
        total = base.copy()
        for d, e in multiplier.items():
            total[d] = total.get(d, 0) + e
            if not total[d]:
                total.pop(d)
        try:
            analysis = analyze_eta_quotient(total, N)
        except ValueError:
            continue
        if not (analysis["modular"] and analysis["holomorphic"]):
            continue
        if target_k is not None and analysis["weight"] != target_k:
            continue
        if analysis["weight"] <= 0:
            continue
        if limit_sturm is not None and analysis["sturm"] is not None and analysis["sturm"] > limit_sturm:
            continue
        results.append({"multiplier": multiplier, "total": total, **analysis})
    results.sort(key=lambda x: (sum(abs(v) for v in x["multiplier"].values()), x["weight"], x["sturm"] or 0))
    return results[:limit_n] if limit_n else results, checked, truncated


def generate_latex_export(base_dict, item):
    M_f = eta_product_latex(item["multiplier"], "f")
    total_eta = eta_product_latex(item["total"], "eta")
    return (
        "% Corrected eta-quotient certificate\n"
        f"% F(q) = {eta_product_latex(base_dict, 'f')}\n"
        f"% M(q) = {M_f}\n"
        f"% q^({format_latex_frac(item['q_shift'])}) F(q)M(q) = {total_eta}\n"
        f"% Weight = {format_latex_frac(item['weight'])}, level = {item['N']}\n"
        f"% Newman sums: {item['sum_T']} == 0 (mod 24), "
        f"{item['sum_S']} == 0 (mod 24)\n"
        f"% Character: chi(d) = ({item['character_D']}/d)\n"
        f"% Sturm bound = {item['sturm']}\n"
        f"{M_f}"
    )

# ==========================================
# --- MODULE 1: INFINITE FAMILY MINER ---
# ==========================================
def run_infinite_family_miner():
    st.title("♾️ Infinite-Family Pattern Miner")
    st.markdown("Search finite coefficient data for geometric progression patterns. A returned family is a **conjectural pattern**, not a proof, unless it is later certified by an exact identity or a valid Sturm bound.")

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
        st.caption("Exact pure-Python expansions above roughly 20,000 terms can be very expensive; begin with a smaller search and extend only promising cases.")
        N = st.number_input("Terms to Generate ($N$)", min_value=500, value=10000, step=500)
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
                coeffs = require_integral_coefficients(coeffs, "the congruence sieve")
                
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
            tab1, tab2, tab3 = st.tabs(["✨ Conjectural Geometric Families", "🎯 Finite-data Progressions", "🧮 Series Expansion Data"])
            
            with tab1:
                if not all_families:
                    st.warning("No three-level geometric pattern was detected in this finite search space.")
                else:
                    st.warning(f"Found {len(all_families)} conjectural geometric pattern(s). These are not yet infinite-family proofs.")
                    collected_latex_lines = []
                    
                    for fam in all_families:
                        mod, A0, R, c1, c2 = fam['mod'], fam['A0'], fam['R'], fam['c1'], fam['c2']
                        c1_str = f"\\frac{{{abs(c1.numerator)}}}{{{c1.denominator}}}" if c1.denominator != 1 else str(abs(c1.numerator))
                        c2_str = f"\\frac{{{abs(c2.numerator)}}}{{{c2.denominator}}}" if c2.denominator != 1 else str(abs(c2.numerator))
                        
                        c1_sign = "+" if c1 >= 0 else "-"
                        c2_sign = "+" if c2 >= 0 else "-"
                        
                        display_str = rf"c\left( {A0} \cdot {R}^k \cdot n {c1_sign} {c1_str} \cdot {R}^k {c2_sign} {c2_str} \right) \overset{{?}}{{\equiv}} 0 \pmod {{{mod}}} \quad (k\ge 0)"
                        aligned_str = rf"c\left( {A0} \cdot {R}^k \cdot n {c1_sign} {c1_str} \cdot {R}^k {c2_sign} {c2_str} \right) &\overset{{?}}{{\equiv}} 0 \pmod {{{mod}}} \quad (k\ge 0)"
                        
                        st.latex(display_str)
                        collected_latex_lines.append(aligned_str)
                        
                    bulk_latex_string = "\\begin{aligned}\n" + " \\\\\n".join(collected_latex_lines) + "\n\\end{aligned}"
                    add_to_clipboard("Conjectural geometric families", bulk_latex_string)
                    st.info("The conjectural formulas were sent to the LaTeX clipboard with a question mark over the congruence sign.")
                        
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
    st.title("⛏️ Computational $q$-Series Congruence Miner")
    st.warning("A finite coefficient check finds candidates and counterexamples. It proves a congruence only when a separate exact-dissection or Sturm certificate is supplied.")

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
            F_q = require_integral_coefficients(F_q, "the congruence miner")

            if mode == "Parametric Family Search":
                def build_env(x_val=1):
                    q_obj = QSeries([0, 1] + [0]*limit, limit)
                    def f(n): 
                        if int(n) <= 0: return QSeries([1] + [0]*limit, limit)
                        return QSeries(generate_base_pochhammer(int(n), limit), limit)
                    return {"f": f, "q": q_obj, "X": x_val, "phi": lambda k: gen_phi(int(k), limit), "psi": lambda k: gen_psi(int(k), limit), "G": lambda k: gen_G(int(k), limit), "H": lambda k: gen_H(int(k), limit), "R": lambda k: gen_R(int(k), limit), "fab": lambda a, b: gen_fab(int(a), int(b), limit), "Psi": lambda a, b: gen_Psi_ab(int(a), int(b), limit), "__builtins__": {}}
                
                family_results = []
                python_formula = latex_to_python(latex_input)
                with st.spinner("Scanning..."):
                    for x_val in range(int(x_min), int(x_max) + 1):
                        try:
                            final_series = restricted_eval(python_formula, build_env(x_val))
                            if not isinstance(final_series, QSeries): final_series = QSeries([int(final_series)] + [0]*limit, limit)
                            F_q_param = require_integral_coefficients(final_series.coeffs, f"the X={x_val} congruence search")
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
                                family_results.append({"X Value": x_val, f"Finite-data candidates mod {hunt_M}": ", ".join(found_for_x)})
                                add_to_clipboard(f"Parametric Congruences (X={x_val})", " \\\\\n".join(found_for_x))
                        except Exception as e: pass
                st.info(f"Trivial sub-progressions were filtered. Every displayed row was checked only through q^{limit}.")
                st.table(pd.DataFrame(family_results))

            elif mode == "Single Pattern Check":
                checked, failures = 0, []
                max_n = (limit - B_val) // A_val
                for n_val in range(max_n + 1):
                    idx = A_val * n_val + B_val
                    if idx == 0:
                        continue
                    if idx > limit:
                        break
                    checked += 1
                    if F_q[idx] % M_val != 0:
                        failures.append({"n": n_val, "index": idx, "coefficient": F_q[idx], "residue": F_q[idx] % M_val})
                if checked == 0:
                    st.warning("No positive-index term in this progression lies inside the selected expansion range.")
                elif failures:
                    st.error(f"Counterexample found after checking {checked} term(s).")
                    st.dataframe(pd.DataFrame(failures[:20]), use_container_width=True, hide_index=True)
                else:
                    st.success(f"No counterexample among {checked} checked term(s), through coefficient index {limit}.")
                    lat_str = rf"c({A_val}n + {B_val}) \overset{{?}}{{\equiv}} 0 \pmod{{{M_val}}}"
                    st.latex(lat_str)
                    add_to_clipboard("Finite-data congruence candidate", lat_str)
                    
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
                    st.success(f"Found {len(found_congruences)} finite-data candidate progression(s), checked only through q^{limit}.")
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
                                    add_to_clipboard(f"Finite-data sieve candidate mod {p}", res_lat)
                                    found_for_p = True
                                    break
                        progress_bar.progress((idx + 1) / len(primes))

                if sieve_results:
                    st.success(f"Found finite-data candidates for {len(sieve_results)} prime(s), each checked only through q^{limit}.")
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
                    st.success(f"Found {len(found_matches)} finite-data candidate(s); trivial subsets were ignored and checking stopped at q^{limit}.")
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
            first_term = Fraction(H_coeffs_raw[0])
            if first_term == 0:
                raise ValueError("The extracted progression has zero constant term, so it cannot be normalized as an Euler product without first removing its initial q-power.")
            H_coeffs = [Fraction(c) / first_term for c in H_coeffs_raw]
            a_exponents = compute_euler_exponents(H_coeffs, len(H_coeffs) - 1)

            is_clean = all(isinstance(val, int) for val in a_exponents[1:])
            
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
    st.title("🛡️ Correct Eta-Quotient & Multiplier Lab")
    st.markdown(
        "This module applies the Newman/Gordon–Hughes modularity conditions and "
        "Ligozat cusp orders. It searches for a pole-clearing eta multiplier; it is not "
        "a substitute for the separate Radu progression algorithm. The certificate implemented here is for integral-weight eta quotients."
    )

    with st.sidebar:
        st.header("1. Base f-product")
        latex_input = st.text_area("F(q)", value=r"\frac{1}{f_1 f_2^{36}}", height=90, key="eta_input")
        st.latex(latex_input)
        auto_level = st.checkbox("Automatically raise level to contain all subscripts", value=True)
        requested_N = st.number_input("Requested level N", min_value=1, value=4, step=1)
        st.divider()
        st.header("2. Multiplier search")
        search_all = st.checkbox("Use every divisor of N", value=True)
        targeted = []
        if not search_all:
            targeted = st.multiselect("Allowed multiplier subscripts", get_divisors(int(requested_N)), default=[1])
        c1, c2 = st.columns(2)
        min_e = c1.number_input("Minimum exponent", value=0, step=1)
        max_e = c2.number_input("Maximum exponent", value=24, step=1)
        target_weight_on = st.checkbox("Fix target weight")
        target_k = st.number_input("Target weight", value=12, min_value=1, step=1, disabled=not target_weight_on)
        c3, c4 = st.columns(2)
        max_results = c3.number_input("Maximum results", value=20, min_value=1, max_value=200)
        max_sturm = c4.number_input("Maximum Sturm bound", value=500, min_value=1)
        max_combinations = st.number_input("Maximum search combinations", value=250000, min_value=1000, step=10000)
        run_btn = st.button("Run rigorous eta analysis", type="primary", use_container_width=True)

    if not run_btn:
        return
    try:
        base = parse_eta_product(latex_input)
        support_lcm = lcm_list(list(base)) if base else 1
        N = lcm(int(requested_N), support_lcm) if auto_level else int(requested_N)
        if N != requested_N:
            st.info(f"The level was raised from {requested_N} to {N}, the least common multiple with all f-subscripts.")

        base_analysis = analyze_eta_quotient(base, N)
        tabs = st.tabs(["Base diagnosis", "Valid multipliers"])
        with tabs[0]:
            st.latex(rf"F(q)=q^{{-{format_latex_frac(base_analysis['q_shift'])}}}\,{eta_product_latex(base, 'eta')}")
            rows = [
                ["Weight", str(base_analysis["weight"])],
                [r"Σ δrδ", f"{base_analysis['sum_T']}  (mod 24 = {base_analysis['sum_T']%24})"],
                [r"Σ (N/δ)rδ", f"{base_analysis['sum_S']}  (mod 24 = {base_analysis['sum_S']%24})"],
                ["Integral weight", base_analysis["integral_weight"]],
                ["Newman modularity", base_analysis["modular"]],
                ["Holomorphic at every cusp", base_analysis["holomorphic"]],
            ]
            st.dataframe(pd.DataFrame(rows, columns=["Test", "Value"]), use_container_width=True, hide_index=True)
            cusp_rows = []
            for c, order in base_analysis["orders"].items():
                label = f"c={c} (1/{c})" + (" ≃ ∞" if c == N else "")
                cusp_rows.append([label, str(order), order >= 0])
            st.dataframe(pd.DataFrame(cusp_rows, columns=["Cusp denominator", "Order", "Holomorphic"]), use_container_width=True, hide_index=True)

        allowed = None if search_all else targeted
        with st.spinner("Checking exact modularity conditions and cusp orders..."):
            results, checked, truncated = find_eta_multipliers(
                N, tuple(base.items()), int(min_e), int(max_e),
                int(target_k) if target_weight_on else None,
                tuple(allowed) if allowed else None,
                int(max_results), int(max_sturm), int(max_combinations)
            )
        with tabs[1]:
            st.caption(f"Checked {checked:,} exponent vectors." + (" Search cap reached." if truncated else ""))
            if not results:
                st.warning("No multiplier satisfying all integral-weight, mod-24, and cusp-holomorphy conditions was found in this box.")
                return
            st.success(f"Found {len(results)} rigorously valid candidate(s).")
            for i, item in enumerate(results, 1):
                with st.expander(f"Candidate {i}: weight {item['weight']}, Sturm bound {item['sturm']}", expanded=i == 1):
                    st.latex(rf"M(q)={eta_product_latex(item['multiplier'], 'f')}")
                    st.latex(rf"q^{{{format_latex_frac(item['q_shift'])}}}F(q)M(q)={eta_product_latex(item['total'], 'eta')}")
                    st.write(f"Newman sums: {item['sum_T']} and {item['sum_S']} (both divisible by 24).")
                    st.write(rf"Nebentypus candidate: $\chi(d)=\left(\frac{{{item['character_D']}}}{{d}}\right)$.")
                    cusp_df = pd.DataFrame([
                        {"c": c, "cusp": "∞" if c == N else f"1/{c}", "order": str(v)}
                        for c, v in item["orders"].items()
                    ])
                    st.dataframe(cusp_df, use_container_width=True, hide_index=True)
                    export = generate_latex_export(base, item)
                    st.code(export, language="latex")
                    if st.button("Add certificate to LaTeX clipboard", key=f"eta_cert_{i}"):
                        add_to_clipboard(f"Eta certificate {i}", export)
                        st.toast("Certificate added.")
    except Exception as exc:
        st.error(f"Eta analysis failed: {exc}")

# ==========================================
# --- MODULE 5: VERIFIED DISSECTION ENGINE ---
# ==========================================
def get_sym_env():
    def f(n):
        return SymExpr([SymTerm(1, 0, {int(n): 1})])
    def R(k):
        return SymExpr([SymTerm(1, 0, {}, {("R", int(k)): 1})])
    q_obj = SymExpr([SymTerm(1, 1)])
    return {"f": f, "R": R, "q": q_obj, "X": 1, "__builtins__": {}}


def load_dissections():
    common2 = "Baruah–Das / Hirschhorn; coefficient-verified in app"
    common3 = "Baruah–Das and standard theta dissections; coefficient-verified in app"
    rr5 = "Ramanujan 5-dissection with R(q)=(q,q^4;q^5)_∞/(q^2,q^3;q^5)_∞"
    return [
        {"p":2,"name":"f_1^2","nice_name":"f₁²","latex_lhs":r"f_1^2","latex_rhs":r"\frac{f_2 f_8^5}{f_4^2 f_{16}^2}-2q\frac{f_2 f_{16}^2}{f_8}","source":common2},
        {"p":2,"name":"1/f_1^2","nice_name":"1/f₁²","latex_lhs":r"\frac{1}{f_1^2}","latex_rhs":r"\frac{f_8^5}{f_2^5 f_{16}^2}+2q\frac{f_4^2 f_{16}^2}{f_2^5 f_8}","source":common2},
        {"p":2,"name":"f_1^4","nice_name":"f₁⁴","latex_lhs":r"f_1^4","latex_rhs":r"\frac{f_4^{10}}{f_2^2 f_8^4}-4q\frac{f_2^2 f_8^4}{f_4^2}","source":common2},
        {"p":2,"name":"1/f_1^4","nice_name":"1/f₁⁴","latex_lhs":r"\frac{1}{f_1^4}","latex_rhs":r"\frac{f_4^{14}}{f_2^{14} f_8^4}+4q\frac{f_4^2 f_8^4}{f_2^{10}}","source":common2},
        {"p":2,"name":"f_1 f_3","nice_name":"f₁f₃","latex_lhs":r"f_1f_3","latex_rhs":r"\frac{f_2 f_8^2 f_{12}^4}{f_4^2 f_6 f_{24}^2}-q\frac{f_4^4 f_6 f_{24}^2}{f_2 f_8^2 f_{12}^2}","source":common2},
        {"p":2,"name":"1/(f_1 f_3)","nice_name":"1/(f₁f₃)","latex_lhs":r"\frac{1}{f_1f_3}","latex_rhs":r"\frac{f_8^2 f_{12}^5}{f_2^2 f_4 f_6^4 f_{24}^2}+q\frac{f_4^5 f_{24}^2}{f_2^4 f_6^2 f_8^2 f_{12}}","source":common2},
        {"p":2,"name":"f_3/f_1^3","nice_name":"f₃/f₁³","latex_lhs":r"\frac{f_3}{f_1^3}","latex_rhs":r"\frac{f_4^6 f_6^3}{f_2^9 f_{12}^2}+3q\frac{f_4^2 f_6 f_{12}^2}{f_2^7}","source":common2},
        {"p":2,"name":"f_3^3/f_1","nice_name":"f₃³/f₁","latex_lhs":r"\frac{f_3^3}{f_1}","latex_rhs":r"\frac{f_4^3 f_6^2}{f_2^2 f_{12}}+q\frac{f_{12}^3}{f_4}","source":common2},
        {"p":2,"name":"f_1/f_3","nice_name":"f₁/f₃","latex_lhs":r"\frac{f_1}{f_3}","latex_rhs":r"\frac{f_2 f_{16} f_{24}^2}{f_6^2 f_8 f_{48}}-q\frac{f_2 f_8^2 f_{12} f_{48}}{f_4 f_6^2 f_{16} f_{24}}","source":common2},
        {"p":2,"name":"f_3/f_1","nice_name":"f₃/f₁","latex_lhs":r"\frac{f_3}{f_1}","latex_rhs":r"\frac{f_4 f_6 f_{16} f_{24}^2}{f_2^2 f_8 f_{12} f_{48}}+q\frac{f_6 f_8^2 f_{48}}{f_2^2 f_{16} f_{24}}","source":common2},
        {"p":2,"name":"f_1^2/f_3^2","nice_name":"f₁²/f₃²","latex_lhs":r"\frac{f_1^2}{f_3^2}","latex_rhs":r"\frac{f_2 f_4^2 f_{12}^4}{f_6^5 f_8 f_{24}}-2q\frac{f_2^2 f_8 f_{12} f_{24}}{f_4 f_6^4}","source":common2},
        {"p":2,"name":"f_1/f_5","nice_name":"f₁/f₅","latex_lhs":r"\frac{f_1}{f_5}","latex_rhs":r"\frac{f_2 f_8 f_{20}^3}{f_4 f_{10}^3 f_{40}}-q\frac{f_4^2 f_{40}}{f_8 f_{10}^2}","source":common2},
        {"p":2,"name":"f_5/f_1","nice_name":"f₅/f₁","latex_lhs":r"\frac{f_5}{f_1}","latex_rhs":r"\frac{f_8 f_{20}^2}{f_2^2 f_{40}}+q\frac{f_4^3 f_{10} f_{40}}{f_2^3 f_8 f_{20}}","source":common2},
        {"p":3,"name":"f_1^2/f_2","nice_name":"f₁²/f₂","latex_lhs":r"\frac{f_1^2}{f_2}","latex_rhs":r"\frac{f_9^2}{f_{18}}-2q\frac{f_3 f_{18}^2}{f_6 f_9}","source":common3},
        {"p":3,"name":"f_2/f_1^2","nice_name":"f₂/f₁²","latex_lhs":r"\frac{f_2}{f_1^2}","latex_rhs":r"\frac{f_6^4 f_9^6}{f_3^8 f_{18}^3}+2q\frac{f_6^3 f_9^3}{f_3^7}+4q^2\frac{f_6^2 f_{18}^3}{f_3^6}","source":common3},
        {"p":3,"name":"f_1 f_4/f_2","nice_name":"f₁f₄/f₂","latex_lhs":r"\frac{f_1f_4}{f_2}","latex_rhs":r"\frac{f_3 f_{12} f_{18}^5}{f_6^2 f_9^2 f_{36}^2}-q\frac{f_9 f_{36}}{f_{18}}","source":common3},
        {"p":3,"name":"f_2/(f_1 f_4)","nice_name":"f₂/(f₁f₄)","latex_lhs":r"\frac{f_2}{f_1f_4}","latex_rhs":r"\frac{f_{18}^9}{f_3^2 f_9^3 f_{12}^2 f_{36}^3}+q\frac{f_6^2 f_{18}^3}{f_3^3 f_{12}^3}+q^2\frac{f_6^4 f_9^3 f_{36}^3}{f_3^4 f_{12}^4 f_{18}^3}","source":common3},
        {"p":3,"name":"f_1^3","nice_name":"f₁³","latex_lhs":r"f_1^3","latex_rhs":r"\frac{f_6 f_9^6}{f_3 f_{18}^3}-3qf_9^3+4q^3\frac{f_3^2 f_{18}^6}{f_6^2 f_9^3}","source":common3},
        {"p":3,"name":"f_1 f_2","nice_name":"f₁f₂","latex_lhs":r"f_1f_2","latex_rhs":r"\frac{f_6 f_9^4}{f_3 f_{18}^2}-qf_9f_{18}-2q^2\frac{f_3 f_{18}^4}{f_6 f_9^2}","source":common3},
        {"p":3,"name":"f_2^2/f_1","nice_name":"f₂²/f₁","latex_lhs":r"\frac{f_2^2}{f_1}","latex_rhs":r"\frac{f_6 f_9^2}{f_3 f_{18}}+q\frac{f_{18}^2}{f_9}","source":"Jacobi triple product; uploaded three-core note; coefficient-verified"},
        {"p":5,"name":"f_1","nice_name":"f₁ via R","latex_lhs":r"f_1","latex_rhs":r"f_{25}\left(\frac{1}{R(q^5)}-q-q^2R(q^5)\right)","source":rr5},
        {"p":5,"name":"1/f_1","nice_name":"1/f₁ via R","latex_lhs":r"\frac{1}{f_1}","latex_rhs":r"\frac{f_{25}^5}{f_5^6}\left(\frac{1}{R(q^5)^4}+\frac{q}{R(q^5)^3}+\frac{2q^2}{R(q^5)^2}+\frac{3q^3}{R(q^5)}+5q^4-3q^5R(q^5)+2q^6R(q^5)^2-q^7R(q^5)^3+q^8R(q^5)^4\right)","source":"Ramanujan reciprocal 5-dissection; uploaded DSOME note; coefficient-verified"},
    ]


def symexpr_to_qseries(expr, limit):
    q_series = QSeries([0, 1], limit)
    cache_f, cache_R = {}, {}
    total = QSeries.zero(limit)
    for term in expr.terms:
        if term.q_power < 0:
            raise ValueError("Negative explicit q-powers are not supported in a power-series verification.")
        series = QSeries.one(limit)*term.coeff
        if term.q_power:
            series = series*(q_series**term.q_power)
        for k, exponent in term.etas.items():
            cache_f.setdefault(k, QSeries(generate_base_pochhammer(k, limit), limit))
            series = series*(cache_f[k]**exponent)
        for (name, k), exponent in term.specials.items():
            if name != "R":
                raise ValueError(f"Unknown special factor {name}.")
            cache_R.setdefault(k, gen_R(k, limit))
            series = series*(cache_R[k]**exponent)
        total = total+series
    return total


def verify_dissection_identity(item, limit=90):
    try:
        lhs = _core_expansion_engine(item["latex_lhs"], limit)
        rhs = _core_expansion_engine(item["latex_rhs"], limit)
        mismatch = next((n for n, (a, b) in enumerate(zip(lhs, rhs)) if a != b), None)
        return {"verified": mismatch is None, "mismatch": mismatch, "limit": limit}
    except Exception as exc:
        return {"verified": False, "mismatch": None, "limit": limit, "error": str(exc)}


def verified_dissection_database(limit=90):
    db = load_dissections()
    for item in db:
        item.update(verify_dissection_identity(item, limit))
    return db


def scaled_vector(vector, scale):
    return {k*scale: v for k, v in vector.items()}


def vector_subtract(a, b, multiple=1):
    result = dict(a)
    for k, v in b.items():
        result[k] = result.get(k, 0)-multiple*v
        if not result[k]:
            result.pop(k)
    return result


def sign_compatible(candidate, remaining, p):
    active = False
    for k, v in candidate.items():
        if k % p == 0:
            continue
        active = True
        rem = remaining.get(k, 0)
        if rem == 0 or (rem > 0) != (v > 0) or abs(v) > abs(rem):
            return False
    return active


def find_dissection_plans(target, p, db, max_scale=30, max_identity_power=8,
                           max_terms=1500, max_plans=5):
    candidates = []
    max_index = max(target, default=1)
    env = get_sym_env()
    for item in db:
        if item["p"] != p or not item.get("verified"):
            continue
        lhs = parse_eta_product(item["latex_lhs"])
        rhs = restricted_eval(latex_to_python(item["latex_rhs"]), env)
        minimum = min(lhs)
        upper = min(max_scale, max(1, max_index//minimum + 1))
        for scale in range(1, upper+1):
            vector = scaled_vector(lhs, scale)
            if not any(k % p and target.get(k, 0) for k in vector):
                continue
            candidates.append({"item": item, "scale": scale, "vector": vector,
                               "rhs": rhs.substitute_q(scale), "branches": max(1, rhs.term_count)})

    plans = []
    memo = set()

    def dfs(remaining, chosen, term_estimate):
        active = tuple(sorted((k, v) for k, v in remaining.items() if k % p and v))
        if not active:
            plans.append({"chosen": list(chosen), "residual": remaining, "term_estimate": term_estimate})
            return len(plans) >= max_plans
        state = (active, tuple((c[0], c[1]) for c in chosen), term_estimate)
        if state in memo:
            return False
        memo.add(state)
        coordinate = min(active, key=lambda kv: abs(kv[1]))[0]
        options = [c for c in candidates if c["vector"].get(coordinate) and sign_compatible(c["vector"], remaining, p)]
        options.sort(key=lambda c: (c["branches"], sum(abs(v) for k, v in c["vector"].items() if k % p)))
        for candidate in options:
            rem = remaining
            for count in range(1, max_identity_power+1):
                if not sign_compatible(candidate["vector"], rem, p):
                    break
                new_estimate = term_estimate*(candidate["branches"]**count)
                if new_estimate > max_terms:
                    break
                rem = vector_subtract(rem, candidate["vector"], 1)
                chosen.append((candidates.index(candidate), count))
                if dfs(rem, chosen, new_estimate):
                    return True
                chosen.pop()
        return False

    # The repeated-choice bookkeeping above stores cumulative count entries; normalize after search.
    dfs(dict(target), [], 1)
    normalized = []
    for plan in plans:
        counts = {}
        for idx, count in plan["chosen"]:
            counts[idx] = counts.get(idx, 0)+count
        normalized.append({"factors": [(candidates[idx], count) for idx, count in counts.items()],
                           "residual": plan["residual"], "term_estimate": plan["term_estimate"]})
    normalized.sort(key=lambda pl: (pl["term_estimate"], len(pl["factors"])))
    return normalized


def build_dissection_expression(plan):
    env = get_sym_env()
    residual = SymExpr([SymTerm(1, 0, plan["residual"])])
    expression = residual
    lhs_parts = []
    for candidate, count in plan["factors"]:
        expression = expression*(candidate["rhs"]**count)
        lhs = scale_latex_lhs(candidate["item"]["latex_lhs"], candidate["scale"])
        lhs_parts.append(rf"\left({lhs}\right)^{{{count}}}" if count != 1 else rf"\left({lhs}\right)")
    return expression, lhs_parts


def format_truncated_component(coeffs, max_display=14):
    pieces = []
    for n, coefficient in enumerate(coeffs):
        if coefficient == 0:
            continue
        c = int(coefficient) if isinstance(coefficient, Fraction) and coefficient.denominator == 1 else coefficient
        if n == 0:
            pieces.append(str(c))
        else:
            qpart = "q" if n == 1 else f"q^{{{n}}}"
            if c == 1:
                pieces.append(qpart)
            elif c == -1:
                pieces.append("-"+qpart)
            else:
                pieces.append(f"{c}{qpart}")
        if len(pieces) >= max_display:
            break
    if not pieces:
        return "0"
    return " + ".join(pieces).replace("+ -", "- ")



def format_exact_number(value):
    value = value if isinstance(value, Fraction) else Fraction(value)
    if value.denominator == 1:
        return str(value.numerator)
    return rf"\frac{{{value.numerator}}}{{{value.denominator}}}"


def dissection_library_latex(items):
    lines = []
    for item in items:
        status = "verified" if item.get("verified") else "not verified"
        lines.append(
            rf"% {item['p']}-dissection; {status} through q^{{{item.get('limit', '?')}}}; {item['source']}\n"
            rf"{item['latex_lhs']} &= {item['latex_rhs']}"
        )
    return "\\begin{aligned}\n" + " \\\\\n".join(lines) + "\n\\end{aligned}"


def component_equation_latex(p, r, rhs):
    return rf"\sum_{{n\ge 0}}a({p}n+{r})q^n={rhs}"


def parse_eta_linear_combination(latex_input):
    """Parse finite sums/differences of eta monomials into SymExpr."""
    obj = restricted_eval(latex_to_python(latex_input), get_sym_env())
    if isinstance(obj, SymTerm):
        obj = SymExpr([obj])
    elif isinstance(obj, (int, Fraction)):
        obj = SymExpr([SymTerm(obj)])
    if not isinstance(obj, SymExpr):
        raise ValueError("Enter a finite sum or difference of eta products/quotients.")
    if any(term.q_power < 0 for term in obj.terms):
        raise ValueError("Negative explicit powers of q are not supported.")
    return obj


def compare_symbolic_series(lhs, rhs, limit):
    left = symexpr_to_qseries(lhs, limit).coeffs
    right = symexpr_to_qseries(rhs, limit).coeffs
    mismatch = next((n for n, (a, b) in enumerate(zip(left, right)) if a != b), None)
    return mismatch


def dissect_symbolic_expression_once(expr, p, db, max_scale=30, max_power=8,
                                      max_terms=1500, verify_terms=100):
    """Dissect every eta monomial of a finite linear combination and recombine exactly."""
    total = SymExpr([SymTerm(0)])
    certificate = []
    for term_number, term in enumerate(expr.terms, 1):
        bad_specials = [(name, k) for (name, k) in term.specials if k % p]
        if bad_specials:
            return {
                "success": False,
                "reason": f"Term {term_number} contains a special factor not visibly depending on q^{p}: {bad_specials}.",
            }
        plans = find_dissection_plans(
            term.etas, p, db, int(max_scale), int(max_power), int(max_terms), 8
        )
        if not plans:
            return {
                "success": False,
                "reason": f"No verified {p}-dissection plan was found for term {term_number}: {SymExpr([term]).to_latex()}.",
            }

        accepted = None
        accepted_plan = None
        for plan in plans:
            try:
                expanded, _ = build_dissection_expression(plan)
                prefactor = SymExpr([SymTerm(term.coeff, term.q_power, {}, term.specials)])
                candidate = prefactor * expanded
                if candidate.term_count > max_terms:
                    continue
                if compare_symbolic_series(SymExpr([term]), candidate, int(verify_terms)) is None:
                    accepted = candidate
                    accepted_plan = plan
                    break
            except Exception:
                continue
        if accepted is None:
            return {
                "success": False,
                "reason": f"Candidate plans for term {term_number} failed the independent coefficient audit.",
            }
        total = total + accepted
        if total.term_count > max_terms:
            return {
                "success": False,
                "reason": f"The exact expression exceeded the selected limit of {max_terms} symbolic terms.",
            }
        certificate.append({"term": term, "plan": accepted_plan, "result": accepted})

    mismatch = compare_symbolic_series(expr, total, int(verify_terms))
    if mismatch is not None:
        return {"success": False, "reason": f"Whole-expression verification failed first at q^{mismatch}."}
    try:
        components = total.components(int(p))
    except Exception as exc:
        return {"success": False, "reason": f"The assembled result is not visibly separated by residues: {exc}"}
    return {
        "success": True,
        "expression": total,
        "components": components,
        "certificate": certificate,
        "verified_through": int(verify_terms),
    }


def q_log_product_exponents(coeffs, fit_limit):
    """Return e_n in F(q)=prod_{n>=1}(1-q^n)^{e_n}, using exact arithmetic."""
    fit_limit = min(int(fit_limit), len(coeffs) - 1)
    series = QSeries(coeffs[: fit_limit + 1], fit_limit)
    if series.coeffs[0] != 1:
        raise ValueError("The normalized series must have constant term 1.")
    q_derivative = QSeries([n * series.coeffs[n] for n in range(fit_limit + 1)], fit_limit)
    log_derivative = q_derivative * series.inv()
    product_exponents = [Fraction(0)] * (fit_limit + 1)
    for n in range(1, fit_limit + 1):
        weighted_previous = sum(
            d * product_exponents[d]
            for d in get_divisors(n)
            if d < n
        )
        product_exponents[n] = (-log_derivative.coeffs[n] - weighted_previous) / n
    return product_exponents


def recognize_f_product(component_coeffs, fit_limit=80, min_tail=12):
    """Find a finite f-product candidate by exact Euler-exponent inversion and verify it."""
    exact = [c if isinstance(c, Fraction) else Fraction(c) for c in component_coeffs]
    first = next((n for n, c in enumerate(exact) if c), None)
    if first is None:
        return {"success": True, "zero": True, "latex": "0", "verified_through": len(exact) - 1}
    leading = exact[first]
    normalized = [c / leading for c in exact[first:]]
    available = len(normalized) - 1
    if available < 12:
        return {"success": False, "reason": "Too few coefficients for product recognition."}
    fit_limit = min(int(fit_limit), available)
    try:
        cyclotomic = q_log_product_exponents(normalized, fit_limit)
    except Exception as exc:
        return {"success": False, "reason": str(exc)}
    if any(x.denominator != 1 for x in cyclotomic[1:]):
        return {"success": False, "reason": "Euler exponents are not integral."}

    f_exponents = [Fraction(0)] * (fit_limit + 1)
    for n in range(1, fit_limit + 1):
        f_exponents[n] = cyclotomic[n] - sum(
            f_exponents[d] for d in get_divisors(n) if d < n
        )
    if any(x.denominator != 1 for x in f_exponents[1:]):
        return {"success": False, "reason": "The inferred f-product exponents are not integral."}
    nonzero = [n for n in range(1, fit_limit + 1) if f_exponents[n]]
    last = max(nonzero, default=0)
    if last and fit_limit - last < min(int(min_tail), max(5, fit_limit // 5)):
        return {"success": False, "reason": "No stable zero tail in the inferred f-product exponents."}
    eta_map = {n: int(f_exponents[n]) for n in nonzero}
    candidate = SymExpr([SymTerm(leading, first, eta_map)])
    verification_limit = len(exact) - 1
    candidate_coeffs = symexpr_to_qseries(candidate, verification_limit).coeffs
    mismatch = next((n for n, (a, b) in enumerate(zip(candidate_coeffs, exact)) if a != b), None)
    if mismatch is not None:
        return {"success": False, "reason": f"Candidate fails at q^{mismatch}."}
    latex = candidate.to_latex()
    return {
        "success": True,
        "zero": False,
        "latex": latex,
        "expression": candidate,
        "f_exponents": eta_map,
        "verified_through": verification_limit,
        "leading_shift": first,
    }


def base_p_digits(residue, p, depth):
    digits = []
    value = int(residue)
    for _ in range(int(depth)):
        digits.append(value % int(p))
        value //= int(p)
    return digits


def progression_chain_latex(p, residue, depth):
    digits = base_p_digits(residue, p, depth)
    modulus, current = 1, 0
    labels = []
    for digit in digits:
        current += modulus * digit
        modulus *= p
        labels.append(rf"a({modulus}n+{current})")
    return r"\longrightarrow ".join(labels)


def deep_exact_extraction(expr, p, residue, depth, db, max_scale, max_power,
                          max_terms, verify_terms):
    current = expr
    records = []
    for level, digit in enumerate(base_p_digits(residue, p, depth), 1):
        dissected = dissect_symbolic_expression_once(
            current, p, db, max_scale, max_power, max_terms, verify_terms
        )
        if not dissected.get("success"):
            return {
                "success": False,
                "level": level,
                "reason": dissected.get("reason", "Unknown failure."),
                "records": records,
            }
        current = dissected["components"][digit]
        if current.term_count > max_terms:
            return {
                "success": False,
                "level": level,
                "reason": "The extracted expression became too large.",
                "records": records,
            }
        records.append({"level": level, "digit": digit, "expression": current, "dissection": dissected})
    return {"success": True, "expression": current, "records": records}


def truncated_component_latex(coeffs, modulus, residue, max_display=18):
    rhs = format_truncated_component(coeffs, max_display=max_display)
    return rf"\sum_{{n\ge0}}a({modulus}n+{residue})q^n={rhs}+O(q^{{{len(coeffs)}}})"


def run_dissection_dictionary():
    st.title("📚 Verified Dissection Library & LaTeX Vault")
    st.markdown(
        "Every stored identity is coefficient-audited before use. Each identity and the complete library "
        "can now be copied or downloaded directly as LaTeX."
    )
    verification_limit = st.slider("Verification precision", 30, 180, 100, 10)
    db = verified_dissection_database(verification_limit)
    verified_count = sum(bool(item.get("verified")) for item in db)
    c1, c2, c3 = st.columns(3)
    c1.metric("Stored identities", len(db))
    c2.metric("Passed audit", verified_count)
    c3.metric("Supported dissections", "2, 3, 5")

    p_filter = st.radio("Show", ["All", 2, 3, 5], horizontal=True)
    shown = db if p_filter == "All" else [x for x in db if x["p"] == p_filter]
    all_export = dissection_library_latex(shown)
    with st.expander("Copy/export the complete displayed library", expanded=False):
        render_latex_export(
            "Complete verified dissection library",
            all_export,
            key=f"all_library_{p_filter}_{verification_limit}",
            filename=f"verified_{p_filter}_dissections.tex",
        )
        st.download_button(
            "Download complete standalone LaTeX document",
            data=latex_document("Verified dissection identities", all_export),
            file_name=f"verified_{p_filter}_dissections_document.tex",
            mime="text/x-tex",
            key=f"doc_library_{p_filter}_{verification_limit}",
            use_container_width=True,
        )

    status_df = pd.DataFrame([{
        "p": item["p"], "identity": item["name"], "verified through": item["limit"],
        "status": "verified" if item["verified"] else f"FAILED at {item.get('mismatch')}",
        "source": item["source"]
    } for item in shown])
    st.dataframe(status_df, use_container_width=True, hide_index=True)

    for idx, item in enumerate(shown):
        status_icon = "✅" if item["verified"] else "❌"
        with st.expander(f"{status_icon} {item['p']}-dissection: {item['nice_name']}"):
            identity = rf"{item['latex_lhs']}={item['latex_rhs']}"
            st.latex(identity)
            st.caption(item["source"])
            render_latex_export(
                f"LaTeX for {item['nice_name']}",
                identity,
                key=f"identity_{p_filter}_{idx}_{verification_limit}",
                filename=f"{safe_widget_key(item['name']).lower()}_{item['p']}_dissection.tex",
            )


def run_auto_dissection():
    st.title("🧩 Automatic p-Dissection Solver")
    st.markdown(
        "Enter either a single eta product/quotient or a finite sum or difference of eta monomials. "
        "The solver dissects each term with the verified identity library, recombines the result, "
        "checks coefficients independently, and exports every residue component as LaTeX."
    )
    with st.sidebar:
        st.header("Dissection input")
        latex_input = st.text_area(
            "F(q)",
            value=r"\frac{f_1^2}{f_2}-\frac{f_1^6}{f_2^3}",
            height=100,
            key="auto_dissection_input",
        )
        st.latex(latex_input)
        p_value = st.selectbox("p-dissection", [2, 3, 5], index=1, key="auto_p")
        verify_terms = st.number_input("Verification terms", min_value=40, value=140, step=10, key="auto_verify")
        max_scale = st.number_input("Maximum identity scale", min_value=1, value=30, step=1, key="auto_scale")
        max_power = st.number_input("Maximum identity repetitions", min_value=1, value=8, step=1, key="auto_power")
        max_symbolic_terms = st.number_input("Maximum symbolic branches", min_value=20, value=1800, step=50, key="auto_branches")
        run_btn = st.button("Find p-dissection", type="primary", use_container_width=True, key="auto_run")
    if not run_btn:
        st.info("This solver now accepts sums and differences directly; use the Composite Lab for deeper progressions such as a(8n+7).")
        return

    try:
        input_expr = parse_eta_linear_combination(latex_input)
        db = verified_dissection_database(min(110, int(verify_terms)))
        exact = dissect_symbolic_expression_once(
            input_expr,
            int(p_value),
            db,
            int(max_scale),
            int(max_power),
            int(max_symbolic_terms),
            int(verify_terms),
        )

        tabs = st.tabs(["Exact symbolic result", "Residue extraction", "Coefficient fallback", "Certificate"])
        exact_success = bool(exact.get("success"))
        exact_expr = exact.get("expression")
        exact_components = exact.get("components")

        with tabs[0]:
            if exact_success:
                st.success(
                    f"Exact term-by-term {p_value}-dissection assembled and independently checked through q^{verify_terms}."
                )
                st.latex(rf"F(q)={exact_expr.to_latex()}")
                full_code = rf"F(q)&={exact_expr.to_latex()}"
                render_latex_export(
                    "Exact dissection LaTeX",
                    "\\begin{aligned}\n" + full_code + "\n\\end{aligned}",
                    key=f"auto_exact_{hashlib.md5(latex_input.encode()).hexdigest()}_{p_value}",
                    filename=f"exact_{p_value}_dissection.tex",
                )
            else:
                st.warning("No exact finite closed form could be assembled within the selected identity and branch limits.")
                st.code(exact.get("reason", "No reason returned."))

        coeffs = _core_expansion_engine(latex_input, int(verify_terms))
        with tabs[1]:
            component_lines = []
            for r in range(int(p_value)):
                st.markdown(f"#### Extract coefficients of $q^{{{p_value}n+{r}}}$")
                if exact_success:
                    rhs = exact_components[r].to_latex()
                    equation = component_equation_latex(int(p_value), r, rhs)
                    if rhs == "0":
                        st.success(f"The component a({p_value}n+{r}) vanishes identically in the exact symbolic result.")
                else:
                    component = coeffs[r::int(p_value)]
                    equation = truncated_component_latex(component, int(p_value), r)
                st.latex(equation)
                component_lines.append(equation)
                render_latex_export(
                    f"Component a({p_value}n+{r})",
                    equation,
                    key=f"auto_component_{p_value}_{r}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                    filename=f"component_{p_value}n_plus_{r}.tex",
                )
            if component_lines:
                render_latex_export(
                    "All residue components",
                    "\\begin{aligned}\n" + " \\\\\n".join(line.replace("=", "&=", 1) for line in component_lines) + "\n\\end{aligned}",
                    key=f"auto_all_components_{p_value}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                    filename=f"all_{p_value}_components.tex",
                )
            st.info(r"Extraction rule: retain powers q^{pn+r}, divide by q^r, and replace q^p by q.")

        with tabs[2]:
            st.info("These are coefficient truncations. They remain available even when the identity library cannot produce a closed form.")
            rows = []
            fallback_lines = []
            for r in range(int(p_value)):
                component = coeffs[r::int(p_value)]
                equation = truncated_component_latex(component, int(p_value), r)
                st.latex(equation)
                fallback_lines.append(equation)
                rows.append({"r": r, "first coefficients": ", ".join(str(x) for x in component[:14])})
            st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)
            render_latex_export(
                "Truncated coefficient dissection",
                "\\begin{aligned}\n" + " \\\\\n".join(line.replace("=", "&=", 1) for line in fallback_lines) + "\n\\end{aligned}",
                key=f"auto_fallback_{p_value}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                filename=f"truncated_{p_value}_dissection.tex",
            )

        with tabs[3]:
            if not exact_success:
                st.write("No exact certificate was produced.")
            else:
                st.write("Verified identities used term-by-term:")
                cert_lines = []
                for term_idx, row in enumerate(exact["certificate"], 1):
                    term_latex = SymExpr([row["term"]]).to_latex()
                    st.markdown(f"**Input term {term_idx}:**")
                    st.latex(term_latex)
                    cert_lines.append(rf"% Input term {term_idx}: {term_latex}")
                    for candidate, count in row["plan"]["factors"]:
                        scaled_lhs = scale_latex_lhs(candidate["item"]["latex_lhs"], candidate["scale"])
                        line = rf"\left({scaled_lhs}\right)^{{{count}}}"
                        st.latex(line)
                        st.caption(candidate["item"]["source"])
                        cert_lines.append(line)
                    if row["plan"].get("residual"):
                        residual = eta_product_latex(row["plan"]["residual"], "f")
                        st.write("Residual q^p-series factor:")
                        st.latex(residual)
                        cert_lines.append(rf"\text{{Residual factor: }}{residual}")
                certificate_code = "% Exact term-by-term dissection certificate\n" + "\n".join(cert_lines)
                render_latex_export(
                    "Method certificate LaTeX",
                    certificate_code,
                    key=f"auto_certificate_{p_value}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                    filename=f"certificate_{p_value}_dissection.tex",
                )
    except Exception as exc:
        st.error(f"Dissection analysis failed: {exc}")

def run_composite_dissection_lab():
    st.title("🧪 Composite 2/3-Dissection & Residue Laboratory")
    st.markdown(
        "This module accepts finite sums and differences of eta products. It first performs exact term-by-term "
        "dissection, then compares coefficients, recognizes simple f-products, and supports iterated extractions "
        "such as a(2n+1), a(4n+3), a(8n+7), or a(3^j n+r)."
    )
    with st.sidebar:
        st.header("Composite expression")
        latex_input = st.text_area(
            "F(q)=Σ a(n)qⁿ",
            value=r"\frac{f_1^2}{f_2}-\frac{f_1^6}{f_2^3}",
            height=110,
            key="composite_input",
        )
        st.latex(latex_input)
        p_value = st.selectbox("Dissection base", [2, 3], index=1, key="composite_p")
        verify_terms = st.number_input("Coefficient audit terms", min_value=50, value=180, step=10, key="composite_verify")
        max_scale = st.number_input("Maximum identity scale", min_value=1, value=30, step=1, key="composite_scale")
        max_power = st.number_input("Maximum repetitions", min_value=1, value=10, step=1, key="composite_power")
        max_terms = st.number_input("Maximum symbolic terms", min_value=30, value=2500, step=50, key="composite_terms")
        max_depth_allowed = 4 if int(p_value) == 2 else 3
        default_depth = 3 if int(p_value) == 2 else 2
        depth = st.number_input("Deep extraction depth", min_value=1, max_value=max_depth_allowed, value=default_depth, step=1, key="composite_depth")
        modulus = int(p_value) ** int(depth)
        default_residue = modulus - 1
        residue = st.number_input("Target residue r", min_value=0, max_value=modulus - 1, value=default_residue, step=1, key="composite_residue")
        run_btn = st.button("Run composite laboratory", type="primary", use_container_width=True, key="composite_run")
    if not run_btn:
        st.info("The default example is a difference of two eta quotients. Choose base 3 to obtain a compact exact dissection.")
        return

    try:
        input_expr = parse_eta_linear_combination(latex_input)
        db = verified_dissection_database(min(110, int(verify_terms)))
        exact = dissect_symbolic_expression_once(
            input_expr, int(p_value), db, int(max_scale), int(max_power), int(max_terms), int(verify_terms)
        )
        coeffs = _core_expansion_engine(latex_input, int(verify_terms))
        tabs = st.tabs([
            "Exact composite dissection",
            "Residue components",
            "Deep progression extraction",
            "Coefficient/product recognition",
            "LaTeX report",
        ])
        export_sections = []

        with tabs[0]:
            if exact.get("success"):
                expression = exact["expression"]
                st.success(
                    f"Exact term-by-term {p_value}-dissection found; full coefficient comparison agrees through q^{verify_terms}."
                )
                st.latex(rf"F(q)={expression.to_latex()}")
                code = "\\begin{aligned}\n" + rf"F(q)&={expression.to_latex()}" + "\n\\end{aligned}"
                export_sections.append(("Exact composite dissection", code))
                render_latex_export(
                    "Exact composite dissection",
                    code,
                    key=f"composite_exact_{p_value}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                    filename=f"composite_exact_{p_value}_dissection.tex",
                )
                st.markdown("#### Construction certificate")
                for term_idx, row in enumerate(exact["certificate"], 1):
                    st.markdown(f"**Input term {term_idx}:**")
                    st.latex(SymExpr([row["term"]]).to_latex())
                    for candidate, count in row["plan"]["factors"]:
                        st.latex(
                            rf"\left({scale_latex_lhs(candidate['item']['latex_lhs'], candidate['scale'])}\right)^{{{count}}}"
                        )
                        st.caption(candidate["item"]["source"])
            else:
                st.warning("Exact symbolic assembly was not available.")
                st.code(exact.get("reason", "No reason returned."))
                st.info("The coefficient and product-recognition tabs still provide useful finite-data output.")

        with tabs[1]:
            component_export = []
            cards = st.columns(int(p_value))
            for r in range(int(p_value)):
                with cards[r]:
                    st.metric("Residue", f"{p_value}n+{r}")
                if exact.get("success"):
                    rhs = exact["components"][r].to_latex()
                    equation = component_equation_latex(int(p_value), r, rhs)
                    complexity = exact["components"][r].term_count
                    st.latex(equation)
                    if rhs == "0":
                        st.success(f"The extraction a({p_value}n+{r}) vanishes identically in the exact symbolic result.")
                    elif complexity <= 4:
                        st.success(f"Simple exact component: {complexity} symbolic term(s).")
                    else:
                        st.caption(f"Exact component with {complexity} symbolic terms.")
                else:
                    component = coeffs[r::int(p_value)]
                    equation = truncated_component_latex(component, int(p_value), r)
                    st.latex(equation)
                component_export.append(equation)
                render_latex_export(
                    f"Extracted component a({p_value}n+{r})",
                    equation,
                    key=f"composite_component_{p_value}_{r}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                    filename=f"a_{p_value}n_plus_{r}.tex",
                )
            all_components = "\\begin{aligned}\n" + " \\\\\n".join(
                line.replace("=", "&=", 1) for line in component_export
            ) + "\n\\end{aligned}"
            export_sections.append(("Residue components", all_components))
            st.info(r"To extract a(pn+r): retain q^{pn+r}, divide by q^r, and replace q^p by q.")

        with tabs[2]:
            modulus = int(p_value) ** int(depth)
            residue = int(residue)
            st.markdown(f"### Target progression: $a({modulus}n+{residue})$")
            st.latex(progression_chain_latex(int(p_value), residue, int(depth)))
            deep = deep_exact_extraction(
                input_expr, int(p_value), residue, int(depth), db,
                int(max_scale), int(max_power), int(max_terms), int(verify_terms)
            )
            direct_component = coeffs[residue::modulus]
            deep_equation = None
            if deep.get("success"):
                rhs = deep["expression"].to_latex()
                deep_equation = rf"\sum_{{n\ge0}}a({modulus}n+{residue})q^n={rhs}"
                # Compare against the direct coefficient extraction in its own q variable.
                direct_limit = len(direct_component) - 1
                symbolic_coeffs = symexpr_to_qseries(deep["expression"], direct_limit).coeffs
                mismatch = next((n for n, (a, b) in enumerate(zip(symbolic_coeffs, direct_component)) if a != b), None)
                if mismatch is None:
                    st.success("Exact iterated extraction succeeded and agrees with direct coefficient extraction.")
                    st.latex(deep_equation)
                    if deep["expression"].term_count <= 5:
                        st.success(f"The resulting form is simple: {deep['expression'].term_count} symbolic term(s).")
                    export_sections.append((f"Deep extraction a({modulus}n+{residue})", deep_equation))
                    render_latex_export(
                        f"Exact deep extraction a({modulus}n+{residue})",
                        deep_equation,
                        key=f"deep_exact_{modulus}_{residue}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                        filename=f"a_{modulus}n_plus_{residue}.tex",
                    )
                else:
                    st.warning(f"The symbolic deep result failed direct comparison at coefficient q^{mismatch}; it has been suppressed.")
                    deep_equation = None
            else:
                st.warning(f"Exact iteration stopped at level {deep.get('level', '?')}: {deep.get('reason', 'unknown reason')}")

            if deep_equation is None:
                fallback = truncated_component_latex(direct_component, modulus, residue)
                st.latex(fallback)
                st.caption("Finite coefficient extraction only; this is not an identity proof.")
                export_sections.append((f"Truncated a({modulus}n+{residue})", fallback))
                render_latex_export(
                    f"Truncated extraction a({modulus}n+{residue})",
                    fallback,
                    key=f"deep_truncated_{modulus}_{residue}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                    filename=f"truncated_a_{modulus}n_plus_{residue}.tex",
                )

            recognition = recognize_f_product(direct_component, fit_limit=min(90, len(direct_component)-1))
            if recognition.get("success"):
                if recognition.get("zero"):
                    st.success(f"All computed coefficients in a({modulus}n+{residue}) are zero through the available range.")
                else:
                    candidate = rf"\sum_{{n\ge0}}a({modulus}n+{residue})q^n\overset{{?}}{{=}}{recognition['latex']}"
                    st.markdown("#### Coefficient-recognized simple product candidate")
                    st.latex(candidate)
                    st.caption(
                        f"The candidate agrees through q^{recognition['verified_through']}; a separate proof is still required unless it matches the exact symbolic result above."
                    )

        with tabs[3]:
            st.markdown("### Automatic coefficient comparison across residue classes")
            st.caption(
                "The recognizer converts each extracted series into Euler product exponents and Möbius-inverts them to search for a finite f-product. Matches are computational candidates unless supported by the exact tab."
            )
            rows = []
            recognized_lines = []
            max_scan_depth = min(int(depth), 3)
            for level in range(1, max_scan_depth + 1):
                mod = int(p_value) ** level
                for r in range(mod):
                    component = coeffs[r::mod]
                    rec = recognize_f_product(component, fit_limit=min(80, len(component)-1))
                    if rec.get("success"):
                        if rec.get("zero"):
                            kind, form = "zero in computed range", "0"
                        else:
                            kind, form = "finite f-product candidate", rec["latex"]
                            recognized_lines.append(
                                rf"\sum_{{n\ge0}}a({mod}n+{r})q^n&\overset{{?}}{{=}}{form}"
                            )
                        rows.append({
                            "progression": f"a({mod}n+{r})",
                            "classification": kind,
                            "recognized form": form,
                            "checked coefficients": len(component),
                        })
                    else:
                        nonzero_first = sum(1 for c in component[:20] if c)
                        if nonzero_first <= 3:
                            rows.append({
                                "progression": f"a({mod}n+{r})",
                                "classification": "sparse first 20 terms",
                                "recognized form": "—",
                                "checked coefficients": len(component),
                            })
            if rows:
                st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)
            else:
                st.info("No especially simple or sparse progression was detected within the selected range.")
            if recognized_lines:
                recognized_code = "\\begin{aligned}\n" + " \\\\\n".join(recognized_lines) + "\n\\end{aligned}"
                export_sections.append(("Coefficient-recognized product candidates", recognized_code))
                render_latex_export(
                    "All recognized product candidates",
                    recognized_code,
                    key=f"recognized_all_{p_value}_{depth}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                    filename="recognized_dissection_candidates.tex",
                )

        with tabs[4]:
            if not export_sections:
                st.info("No exportable result was produced.")
            else:
                report_body = "\n\n".join(
                    f"% --- {title} ---\n{code}" for title, code in export_sections
                )
                render_latex_export(
                    "Complete analysis LaTeX",
                    report_body,
                    key=f"composite_report_{p_value}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                    filename="composite_dissection_report.tex",
                )
                st.download_button(
                    "Download standalone LaTeX report",
                    data=latex_document("Composite dissection analysis", report_body),
                    file_name="composite_dissection_report_standalone.tex",
                    mime="text/x-tex",
                    key=f"composite_standalone_{p_value}_{hashlib.md5(latex_input.encode()).hexdigest()}",
                    use_container_width=True,
                )
    except Exception as exc:
        st.error(f"Composite dissection analysis failed: {exc}")


# Backward-compatible strategist now delegates to the exact solver.
def run_strategy_suggestor():
    run_auto_dissection()

# ==========================================
# --- MASTER NAVIGATION CONTROLLER ---
# ==========================================
st.sidebar.title("🧭 Main Menu")
app_mode = st.sidebar.selectbox("Select Application Module:", [
    "⛏️ Congruence Miner", 
    "♾️ Infinite Family Miner", 
    "🌀 Euler Product Explorer",
    "🛡️ Correct Eta-Multiplier Lab", 
    "📚 Verified Dissection Library",
    "🧩 Automatic p-Dissection Solver",
    "🧪 Composite & Residue Dissection Lab"
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
elif app_mode == "🛡️ Correct Eta-Multiplier Lab": run_eta_multiplier()
elif app_mode == "📚 Verified Dissection Library": run_dissection_dictionary()
elif app_mode == "🧩 Automatic p-Dissection Solver": run_auto_dissection()
elif app_mode == "🧪 Composite & Residue Dissection Lab": run_composite_dissection_lab()
