import streamlit as st
import math
import pandas as pd
from itertools import product
from fractions import Fraction

# --- Page Configuration ---
st.set_page_config(page_title="Eta-Multiplier Pro", layout="wide")

# --- Math Utilities ---
def get_divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def constrained_partitions(n, k):
    """Generates non-negative combinations for strict target k searches."""
    if n == 1:
        yield [k]
        return
    for i in range(k + 1):
        for p in constrained_partitions(n - 1, k - i):
            yield [i] + p

def get_sturm_bound(k, N):
    """Calculates the Sturm Bound for Gamma0(N)."""
    index, temp_n, d, primes = N, N, 2, set()
    while d * d <= temp_n:
        if temp_n % d == 0:
            primes.add(d)
            while temp_n % d == 0: temp_n //= d
        d += 1
    if temp_n > 1: primes.add(temp_n)
    for p in primes: index = index * (1 + 1/p)
    return math.ceil((k * index) / 12)

def format_latex_frac(frac):
    """Converts a Fraction to a large LaTeX display fraction."""
    if frac.denominator == 1:
        return f"{frac.numerator}"
    return f"\\dfrac{{{frac.numerator}}}{{{frac.denominator}}}"

# --- LaTeX Generator ---
def generate_latex_export(t, r, N, base_profile, item):
    """Generates a formatted LaTeX string for academic papers."""
    base_parts = []
    for d, p in base_profile.items():
        if p == 1: base_parts.append(f"\\eta({d}z)")
        elif p != 0: base_parts.append(f"\\eta^{{{p}}}({d}z)")
    base_lat = "".join(base_parts)

    mult_parts = []
    for d, p in item['multiplier'].items():
        if p == 1: mult_parts.append(f"\\eta({d}z)")
        elif p != 0: mult_parts.append(f"\\eta^{{{p}}}({d}z)")
    mult_lat = "".join(mult_parts) if mult_parts else "1"

    latex_code = f"""% --- Auto-Generated Modular Form Data ---
\\begin{{align*}}
    \\text{{Level }} (N) &= {N} \\\\
    \\text{{Target}} &\\equiv {r
