import streamlit as st
import math
from itertools import product
from fractions import Fraction

# --- 1. Page Configuration (Wide layout, like Desmos) ---
st.set_page_config(page_title="Eta-Multiplier Finder", layout="wide", initial_sidebar_state="expanded")

# --- Math Functions ---
def gcd(a, b): 
    return math.gcd(a, b)

def get_divisors(n): 
    return [d for d in range(1, n + 1) if n % d == 0]

def find_eta_multiplier(target_mod, target_rem, level, base_eta_profile, max_exponent=20):
    divisors = get_divisors(level)
  allowed_divisors = divisors
    search_space = [range(max_exponent + 1) for _ in allowed_divisors]
    valid_multipliers = []

    for exponents in product(*search_space):
        total_profile = base_eta_profile.copy()
        for i, div in enumerate(allowed_divisors):
            if div in total_profile:
                total_profile[div] += exponents[i]
            else:
                total_profile[div] = exponents[i]
                
        if sum(d * r for d, r in total_profile.items()) % 24 != 0: 
            continue
        if sum((level // d) * r for d, r in total_profile.items()) % 24 != 0: 
            continue
            
        is_holomorphic = True
        for d in divisors:
            cusp_sum = sum((Fraction(gcd(d, delta)**2, delta) * r) for delta, r in total_profile.items())
            if cusp_sum < 0:
                is_holomorphic = False
                break
        if not is_holomorphic: 
            continue
            
        b_sum = sum(div * power for div, power in zip(allowed_divisors, exponents))
        b = b_sum / 24
        
        if b.is_integer() and (-int(b) % target_mod) == target_rem:
            weight_k = sum(total_profile.values()) / 2
            if weight_k.is_integer() and weight_k > 0:
                valid_multipliers.append({
                    'multiplier_exponents': dict(zip(allowed_divisors, exponents)),
                    'weight_k': int(weight_k),
                    'shift_b': int(b)
                })

    valid_multipliers.sort(key=lambda x: x['weight_k'])
    return valid_multipliers

# --- UI Redesign (The "Desmos" Feel) ---

st.title("✨ Modular Form Eta-Multiplier Finder")
st.markdown("Find the optimal $\eta$-quotient multiplier to prove partition congruences via Sturm's bound.")

# --- 2. Sidebar for Inputs (Left Panel) ---
with st.sidebar:
    st.header("⚙️ Configuration")
    
    st.subheader("Target Congruence")
    col1, col2 = st.columns(2)
    with col1:
        target_mod = st.number_input("Modulo (t)", min_value=1, value=24)
    with col2:
        target_rem = st.number_input("Remainder (r)", min_value=0, value=16)
        
    st.subheader("Search Parameters")
    level = st.number_input("Search Level (N)", min_value=1, value=48)
    
    st.markdown("**Base Eta Profile**")
    st.markdown("*Format: `arg:power` (e.g., `4:1` for $\eta(4z)^1$)*")
    profile_input = st.text_input("Profile Input", value="4:1, 6:2, 1:-1, 3:-1, 12:-1", label_visibility="collapsed")
    
    max_exp = st.number_input("Max Exponent", min_value=1, value=20)
    
    st.markdown("---")
    # Make the button prominent and span the whole sidebar
    calculate_btn = st.button("🔍 Find Multipliers", use_container_width=True, type="primary")

# --- 3. Main Panel for Results (Right Panel) ---
if calculate_btn:
    with st.spinner("Crunching the numbers... this might take a moment."):
        try:
            base_profile = {}
            for item in profile_input.split(","):
                arg, power = item.split(":")
                base_profile[int(arg.strip())] = int(power.strip())
            
            results = find_eta_multiplier(target_mod, target_rem, level, base_profile, max_exp)
            
            if results:
                st.success(f"🎉 Found {len(results)} valid multipliers! Showing top options:")
                st.divider()
                
                for i, best in enumerate(results[:10]):
                    with st.container():
                        st.subheader(f"Option {i+1}")
                        
                        # Use columns to separate the stats from the math formula
                        stat_col, math_col = st.columns([1, 2])
                        
                        with stat_col:
                            st.metric("Minimal Weight (k)", best['weight_k'])
                            st.metric("Shift (b)", best['shift_b'])
                            
                        with math_col:
                            st.markdown("**Multiplier Function:**")
                            # Build a beautiful LaTeX string for the output
                            latex_str = ""
                            for divisor, power in best['multiplier_exponents'].items():
                                if power > 0:
                                    if power == 1:
                                        latex_str += f"\\eta({divisor}z)"
                                    else:
                                        latex_str += f"\\eta^{{{power}}}({divisor}z)"
                            
                            # Render it as a massive, clean math equation
                            st.latex(latex_str)
                            
                        st.divider()
            else:
                st.info("No valid multiplier found. Try increasing the level or max exponent.")
        except Exception as e:
            st.error(f"Error parsing input. Please check your formatting. Details: {e}")
else:
    # A friendly placeholder before they click the button
    st.info("👈 Enter your parameters in the sidebar and click **Find Multipliers** to begin.")
