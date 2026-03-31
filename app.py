import streamlit as st
import math
from itertools import product
from fractions import Fraction

# --- 1. Page Configuration ---
st.set_page_config(page_title="Eta-Multiplier Finder", layout="wide", initial_sidebar_state="expanded")

# Initialize Session State for History
if 'history' not in st.session_state:
    st.session_state.history = []

# --- Math Functions ---
def gcd(a, b): 
    return math.gcd(a, b)

def get_divisors(n): 
    return [d for d in range(1, n + 1) if n % d == 0]

def find_eta_multiplier(target_mod, target_rem, level, base_eta_profile, max_exponent=20):
    divisors = get_divisors(level)
    allowed_divisors = [d for d in divisors if d % target_mod == 0]
    search_space = [range(max_exponent + 1) for _ in allowed_divisors]
    valid_multipliers = []

    for exponents in product(*search_space):
        total_profile = base_eta_profile.copy()
        for i, div in enumerate(allowed_divisors):
            total_profile[div] = total_profile.get(div, 0) + exponents[i]
                
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

# --- UI Redesign ---

st.title("✨ Modular Form Eta-Multiplier Finder")

# --- 2. Sidebar for Inputs ---
with st.sidebar:
    st.header("⚙️ Configuration")
    
    target_mod = st.number_input("Modulo (t)", min_value=1, value=24)
    target_rem = st.number_input("Remainder (r)", min_value=0, value=16)
    level = st.number_input("Search Level (N)", min_value=1, value=48)
    
    st.markdown("**Base Eta Profile**")
    profile_input = st.text_input("Profile Input", value="4:1, 6:2, 1:-1, 3:-1, 12:-1")
    max_exp = st.number_input("Max Exponent", min_value=1, value=20)
    
    st.markdown("---")
    calculate_btn = st.button("🔍 Find Multipliers", use_container_width=True, type="primary")

# --- 3. Main Layout: Results & History ---
res_tab, hist_tab = st.tabs(["📊 Current Results", "history_toggle History Log"])

with res_tab:
    if calculate_btn:
        with st.spinner("Crunching numbers..."):
            try:
                base_profile = {int(i.split(":")[0].strip()): int(i.split(":")[1].strip()) for i in profile_input.split(",")}
                results = find_eta_multiplier(target_mod, target_rem, level, base_profile, max_exp)
                
                if results:
                    # Save to History (Limit 300)
                    new_entry = {
                        "params": f"Mod {target_mod}, Rem {target_rem}, Lvl {level}",
                        "best_weight": results[0]['weight_k'],
                        "results": results[:5] # Store top 5
                    }
                    st.session_state.history.insert(0, new_entry)
                    if len(st.session_state.history) > 300:
                        st.session_state.history.pop()

                    st.success(f"Found {len(results)} multipliers!")
                    for i, best in enumerate(results[:10]):
                        with st.expander(f"Option {i+1}: Weight {best['weight_k']}, Shift {best['shift_b']}", expanded=(i==0)):
                            latex_str = "".join([f"\\eta^{{{p}}}({d}z)" if p > 1 else f"\\eta({d}z)" for d, p in best['multiplier_exponents'].items() if p > 0])
                            st.latex(latex_str)
                else:
                    st.info("No valid multiplier found.")
            except Exception as e:
                st.error(f"Error: {e}")
    else:
        st.info("👈 Set parameters and click Find Multipliers.")

with hist_tab:
    st.header("📜 Search History (Up to 300)")
    if not st.session_state.history:
        st.write("No history yet.")
    else:
        if st.button("🗑️ Clear All History"):
            st.session_state.history = []
            st.rerun()

        for idx, item in enumerate(st.session_state.history):
            cols = st.columns([3, 1])
            with cols[0]:
                st.write(f"**{item['params']}** — Best Weight: {item['best_weight']}")
            with cols[1]:
                if st.button(f"Delete", key=f"del_{idx}"):
                    st.session_state.history.pop(idx)
                    st.rerun()
            st.divider()
