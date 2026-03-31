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
    if n == 1:
        yield [k]
        return
    for i in range(k + 1):
        for p in constrained_partitions(n - 1, k - i):
            yield [i] + p

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

def calculate_cusp_orders(profile, level):
    divs = get_divisors(level)
    # Returns fractions as strings/objects for display
    return {d: sum((Fraction(math.gcd(d, delta)**2, 24 * delta) * r) 
            for delta, r in profile.items()) for d in divs}

def format_latex_frac(frac):
    """Converts a Fraction object to a LaTeX string."""
    if frac.denominator == 1:
        return f"{frac.numerator}"
    return f"\\frac{{{frac.numerator}}}{{{frac.denominator}}}"

# --- Narrowed Core Logic ---
def find_eta_multipliers(target_mod, target_rem, level, base_profile, max_exp, target_k=None):
    divisors = get_divisors(level)
    allowed_divs = [d for d in divisors if d % target_mod == 0]
    results = []
    
    base_weight_2k = sum(base_profile.values())
    
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
        
        k_val = sum(total_profile.values()) / 2
        if not k_val.is_integer() or k_val <= 0: continue
        k = int(k_val)

        if sum(d * r for d, r in total_profile.items()) % 24 != 0: continue
        if sum((level // d) * r for d, r in total_profile.items()) % 24 != 0: continue
            
        cusp_orders = calculate_cusp_orders(total_profile, level)
        if any(order < 0 for order in cusp_orders.values()): continue
            
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
    
    st.markdown("---")
    st.subheader("Base Eta Quotient")
    st.caption("Enter divisors ($d$) and powers ($r$) for $\prod \eta(dz)^r$")
    # Improved Table Input
    input_df = pd.DataFrame([{"Divisor (d)": 1, "Power (r)": -1}, {"Divisor (d)": 5, "Power (r)": 1}])
    edited_df = st.data_editor(input_df, num_rows="dynamic", use_container_width=True)
    
    st.divider()
    k_mode = st.radio("Search Optimization", ["Auto (Minimal k)", "Strict (Target k)"])
    target_k = st.number_input("Target k", value=12) if k_mode == "Strict (Target k)" else None
    max_e = st.number_input("Max Exponent (for Auto)", value=10)

    if st.button("🔍 Run Optimized Analysis", type="primary", use_container_width=True):
        try:
            # Convert dataframe to dict
            base = dict(zip(edited_df["Divisor (d)"].astype(int), edited_df["Power (r)"].astype(int)))
            res = find_eta_multipliers(t, r, N, base, max_e, target_k)
            st.session_state.current_results = res if res else "NOT_FOUND"
        except Exception as e:
            st.error(f"Input Error: Please ensure divisors and powers are integers.")

# --- Display Results ---
if "current_results" in st.session_state:
    if st.session_state.current_results == "NOT_FOUND":
        st.error(f"❌ No valid multipliers exist for these parameters.")
    else:
        st.success(f"Found {len(st.session_state.current_results)} candidates.")
        for idx, item in enumerate(st.session_state.current_results[:10]):
            with st.expander(f"Candidate {idx+1} | k = {item['k']} | Sturm = {item['sturm']}", expanded=(idx==0)):
                
                col1, col2 = st.columns([1, 1])
                
                with col1:
                    st.markdown("**Multiplier Function**")
                    mult_lat = "".join([f"\\eta^{{{v}}}({k}z)" if v > 1 else f"\\eta({k}z)" 
                                      for k, v in item['multiplier'].items() if v > 0])
                    st.latex(f"M(z) = {mult_lat}")
                    st.metric("Shift (b)", item['b'])
                
                with col2:
                    st.markdown("**Orders at Cusps**")
                    # Create a nice looking table for cusp orders
                    cusp_data = []
                    for c, val in item['cusp_orders'].items():
                        cusp_data.append({"Cusp": f"1/{c}", "Order": f"${format_latex_frac(val)}$"})
                    
                    st.table(pd.DataFrame(cusp_data))
