import streamlit as st
import math
from itertools import product
from fractions import Fraction

# --- 1. Page Configuration & Memory Setup ---
st.set_page_config(page_title="Eta-Multiplier Finder", layout="wide", initial_sidebar_state="expanded")

# Initialize the history memory bank if it doesn't exist yet
if 'history' not in st.session_state:
    st.session_state.history = []

# --- Math Functions ---
def gcd(a, b): 
    return math.gcd(a, b)

def get_divisors(n): 
    return [d for d in range(1, n + 1) if n % d == 0]

def find_eta_multiplier(target_mod, target_rem, level, base_eta_profile, min_exponent=0, max_exponent=20):
    divisors = get_divisors(level)
    
    # We use all divisors to ensure prime modulos (like 43) work perfectly
    allowed_divisors = divisors 
    
    # Search space now correctly handles negative minimums
    search_space = [range(min_exponent, max_exponent + 1) for _ in allowed_divisors]
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
            # Using Fraction ensures perfect math for cusp checks
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

# Create Tabs for a cleaner layout
tab_calc, tab_history = st.tabs(["🧮 Calculator", "📜 Search History"])

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
    
    st.markdown("**Exponent Search Range**")
    exp_col1, exp_col2 = st.columns(2)
    with exp_col1:
        min_exp = st.number_input("Min (Negative)", value=-3)
    with exp_col2:
        max_exp = st.number_input("Max (Positive)", value=20)
        
    st.markdown("---")
    calculate_btn = st.button("🔍 Find Multipliers", use_container_width=True, type="primary")

# --- 3. Main Panel for Results (Right Panel) ---
with tab_calc:
    if calculate_btn:
        with st.spinner(f"Crunching the numbers between {min_exp} and {max_exp}..."):
            try:
                base_profile = {}
                for item in profile_input.split(","):
                    arg, power = item.split(":")
                    base_profile[int(arg.strip())] = int(power.strip())
                
                results = find_eta_multiplier(target_mod, target_rem, level, base_profile, min_exp, max_exp)
                
                if results:
                    st.success("🎉 **Success! We found the math to prove your congruence.**")
                    st.markdown(f"""
                    **What this means:** For your base function, if you want to prove that the remainder is always **{target_rem}** when dividing by **{target_mod}**, you can multiply your function by any of the $\eta$-quotients below. 
                    
                    *We have sorted them from the simplest (lowest modular weight) to the most complex.*
                    """)
                    st.divider()
                    
                    # --- Save to History ---
                    best_latex_str = ""
                    for divisor, power in results[0]['multiplier_exponents'].items():
                        if power != 0:
                            if power == 1:
                                best_latex_str += f"\\eta({divisor}z)"
                            else:
                                best_latex_str += f"\\eta^{{{power}}}({divisor}z)"
                    
                    history_record = {
                        "mod": target_mod,
                        "rem": target_rem,
                        "level": level,
                        "profile": profile_input,
                        "best_multiplier": best_latex_str,
                        "weight": results[0]['weight_k']
                    }
                    
                    st.session_state.history.insert(0, history_record)
                    st.session_state.history = st.session_state.history[:300]
                    
                    # --- Display Results ---
                    for i, best in enumerate(results[:10]):
                        with st.container():
                            st.subheader(f"Option {i+1}")
                            
                            stat_col, math_col = st.columns([1, 2])
                            
                            with stat_col:
                                st.metric("Minimal Weight (k)", best['weight_k'])
                                st.metric("Shift (b)", best['shift_b'])
                                
                            with math_col:
                                st.markdown("**Multiplier Function:**")
                                latex_str = ""
                                for divisor, power in best['multiplier_exponents'].items():
                                    if power != 0:
                                        if power == 1:
                                            latex_str += f"\\eta({divisor}z)"
                                        else:
                                            latex_str += f"\\eta^{{{power}}}({divisor}z)"
                                
                                st.latex(latex_str)
                                
                            st.divider()
                else:
                    st.warning(f"**No results found.** We checked all combinations of exponents between {min_exp} and {max_exp} for Level {level}, but none perfectly satisfied the rules. Try widening your exponent range or increasing the Search Level!")
            except Exception as e:
                st.error(f"Error parsing input. Please check your formatting. Details: {e}")
    else:
        st.info("👈 Enter your parameters in the sidebar and click **Find Multipliers** to begin. Your results will appear here, and past searches will be saved in the History tab!")

# --- 4. History Panel ---
with tab_history:
    st.header("Search History")
    
    hist_col1, hist_col2 = st.columns([3, 1])
    with hist_col1:
        st.markdown(f"*Showing your last {len(st.session_state.history)} searches (Max: 300).*")
    with hist_col2:
        if len(st.session_state.history) > 0:
            if st.button("🗑️ Clear All History", use_container_width=True):
                st.session_state.history = []
                st.rerun()
    
    st.divider()

    if len(st.session_state.history) == 0:
        st.info("Your history is currently empty. Run a calculation to see it saved here!")
    else:
        for idx, record in enumerate(st.session_state.history):
            with st.expander(f"Search {len(st.session_state.history) - idx}: Modulo {record['mod']} (Remainder {record['rem']})"):
                st.markdown(f"**Base Profile:** `{record['profile']}`")
                st.markdown(f"**Search Level:** {record['level']}")
                st.markdown("**Best Multiplier Found (Lowest Weight):**")
                st.latex(record['best_multiplier'])
                st.markdown(f"*Weight (k): {record['weight']}*")
                
                if st.button("🗑️ Delete this entry", key=f"del_{idx}"):
                    st.session_state.history.pop(idx)
                    st.rerun()
