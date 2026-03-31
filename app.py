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
    """Generates combinations of exponents that sum exactly to a target."""
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

def calculate_cusp_orders(profile, level):
    """Calculates the exact vanishing order at each cusp."""
    divs = get_divisors(level)
    return {d: sum((Fraction(math.gcd(d, delta)**2, 24 * delta) * r) 
            for delta, r in profile.items()) for d in divs}

def format_latex_frac(frac):
    """Converts a Fraction to a large LaTeX display fraction."""
    if frac.denominator == 1:
        return f"{frac.numerator}"
    return f"\\dfrac{{{frac.numerator}}}{{{frac.denominator}}}"

# --- Narrowed Core Logic ---
def find_eta_multipliers(target_mod, target_rem, level, base_profile, max_exp, target_k=None):
    divisors = get_divisors(level)
    allowed_divs = [d for d in divisors if d % target_mod == 0]
    results = []
    
    base_weight_2k = sum(base_profile.values())
    
    # Choose Search Strategy
    if target_k is not None:
        required_exp_sum = (2 * target_k) - base_weight_2k
        if required_exp_sum < 0: return []
        search_iterator = constrained_partitions(len(allowed_divs), required_exp_sum)
    else:
        search_iterator = product(range(max_exp + 1), repeat=len(allowed_divs))

    for exponents in search_iterator:
        current_multiplier = dict(zip(allowed_divs, exponents))
        total_profile = base_profile.copy()
        for d, exp in current_multiplier.items():
            total_profile[d] = total_profile.get(d, 0) + exp
        
        # 1. Check Weight
        k_val = sum(total_profile.values()) / 2
        if not k_val.is_integer() or k_val <= 0: continue
        k = int(k_val)

        # 2. Check Mod 24 Conditions
        if sum(d * r for d, r in total_profile.items()) % 24 != 0: continue
        if sum((level // d) * r for d, r in total_profile.items()) % 24 != 0: continue
            
        # 3. Check Holomorphicity at Cusps
        cusp_orders = calculate_cusp_orders(total_profile, level)
        if any(order < 0 for order in cusp_orders.values()): continue
            
        # 4. Check Shift (b)
        b_num = sum(d * exp for d, exp in current_multiplier.items())
        if b_num % 24 != 0: continue
        b = b_num // 24
        
        if (-b % target_mod) == target_rem:
            results.append({
                'multiplier': current_multiplier, 'k': k, 'b': b,
                'cusp_orders': cusp_orders, 'sturm': get_sturm_bound(k, level)
            })
            
    return sorted(results, key=lambda x: x['k'])

# --- UI Layout ---
st.title("🛡️ Narrowed Eta-Multiplier Finder")

with st.sidebar:
    st.header("⚙️ Configuration")
    t = st.number_input("Modulo (t)", value=24)
    r = st.number_input("Remainder (r)", value=16)
    N = st.number_input("Level (N)", value=48)
    
    st.divider()
    st.subheader("Base Eta Quotient")
    st.caption("Click to edit. Add empty rows to create new terms.")
    
    # Initialize default table data
    if 'input_data' not in st.session_state:
        st.session_state.input_data = pd.DataFrame([
            {"Divisor (d)": 1, "Power (r)": -1},
            {"Divisor (d)": 5, "Power (r)": 1}
        ])

    # Interactive Data Editor
    edited_df = st.data_editor(
        st.session_state.input_data, 
        num_rows="dynamic", 
        use_container_width=True,
        hide_index=True,
        column_config={
            "Divisor (d)": st.column_config.NumberColumn(format="%d", min_value=1),
            "Power (r)": st.column_config.NumberColumn(format="%d")
        }
    )
    
    st.divider()
    k_mode = st.radio("Search Optimization", ["Auto (Minimal k)", "Strict (Target k)"])
    target_k = st.number_input("Target k", value=12) if k_mode == "Strict (Target k)" else None
    max_e = st.number_input("Max Exponent (for Auto)", value=10)

    if st.button("🔍 Run Optimized Analysis", type="primary", use_container_width=True):
        try:
            # --- BULLETPROOF CLEANING ---
            clean_df = edited_df.replace('', pd.NA).dropna(subset=["Divisor (d)", "Power (r)"])
            clean_df = clean_df[clean_df["Divisor (d)"] > 0]
            
            if clean_df.empty:
                st.error("Please provide at least one valid Divisor and Power.")
            else:
                base = dict(zip(clean_df["Divisor (d)"].astype(int), clean_df["Power (r)"].astype(int)))
                res = find_eta_multipliers(t, r, N, base, max_e, target_k)
                st.session_state.current_results = res if res else "NOT_FOUND"
        except Exception as e:
            st.error(f"Analysis failed. Please check your inputs. Details: {e}")

# --- Display Results ---
if "current_results" in st.session_state:
    if st.session_state.current_results == "NOT_FOUND":
        st.error("❌ No valid multipliers exist for these parameters.")
    else:
        st.success(f"Found {len(st.session_state.current_results)} candidates.")
        
        for idx, item in enumerate(st.session_state.current_results[:10]):
            with st.expander(f"Candidate {idx+1} | k = {item['k']} | Sturm = {item['sturm']}", expanded=(idx==0)):
                
                col1, col2 = st.columns([1, 1.2])
                
                with col1:
                    st.markdown("**Multiplier Function**")
                    mult_lat = "".join([f"\\eta^{{{v}}}({k}z)" if v > 1 else f"\\eta({k}z)" 
                                      for k, v in item['multiplier'].items() if v > 0])
                    st.latex(f"M(z) = {mult_lat}")
                    st.metric("Shift (b)", item['b'])
                
                with col2:
                    st.markdown("**Orders at Cusps ($ord(f, c)$)**")
                    
                    # Markdown Table for perfect LaTeX Fraction rendering
                    md_table = "| Cusp ($1/d$) | Vanishing Order |\n| :---: | :---: |\n"
                    for c, val in item['cusp_orders'].items():
                        md_table += f"| $1/{c}$ | ${format_latex_frac(val)}$ |\n"
                    
                    st.markdown(md_table)
