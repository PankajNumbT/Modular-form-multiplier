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

def find_eta_multiplier(target_mod, target_rem, level, base_eta_profile, max_exponent=10):
    divisors = get_divisors(level)
    # Only multipliers whose arguments are multiples of target_mod are useful for specific shifts
    allowed_divisors = [d for d in divisors if d % target_mod == 0]
    valid_multipliers = []
    
    # Pre-calculate base stats to speed up the loop
    base_weight_sum = sum(base_eta_profile.values())
    base_delta_sum = sum(d * r for d, r in base_eta_profile.items())
    base_epsilon_sum = sum((level // d) * r for d, r in base_eta_profile.items())

    # The bottleneck is the Cartesian product. 
    # We use a generator to keep memory usage low.
    search_space = product(range(max_exponent + 1), repeat=len(allowed_divisors))

    for exponents in search_space:
        # --- OPTIMIZATION 1: Weight Check ---
        # Weight k = (sum of exponents) / 2. Must be integer > 0.
        added_weight = sum(exponents)
        total_weight_2k = base_weight_sum + added_weight
        if total_weight_2k <= 0 or total_weight_2k % 2 != 0:
            continue
            
        # --- OPTIMIZATION 2: Level Divisibility (24-check) ---
        added_delta_sum = sum(d * e for d, e in zip(allowed_divisors, exponents))
        if (base_delta_sum + added_delta_sum) % 24 != 0:
            continue
            
        added_epsilon_sum = sum((level // d) * e for d, e in zip(allowed_divisors, exponents))
        if (base_epsilon_sum + added_epsilon_sum) % 24 != 0:
            continue

        # --- OPTIMIZATION 3: Shift Check ---
        # Calculate b = (sum delta*r) / 24. We need -b ≡ r (mod t)
        b_sum = base_delta_sum + added_delta_sum
        b = b_sum // 24
        if (-b % target_mod) != target_rem:
            continue

        # --- HEAVY LIFTING: Holomorphicity at Cusps ---
        total_profile = base_eta_profile.copy()
        for i, div in enumerate(allowed_divisors):
            total_profile[div] = total_profile.get(div, 0) + exponents[i]
            
        is_holomorphic = True
        for d in divisors:
            # The valence formula at cusp 1/d
            cusp_sum = sum((Fraction(gcd(d, delta)**2, delta) * r) for delta, r in total_profile.items())
            if cusp_sum < 0:
                is_holomorphic = False
                break
        
        if is_holomorphic:
            valid_multipliers.append({
                'multiplier_exponents': dict(zip(allowed_divisors, exponents)),
                'weight_k': int(total_weight_2k // 2),
                'shift_b': int(b)
            })
            # Limit results per search to prevent UI lag
            if len(valid_multipliers) >= 50:
                break

    valid_multipliers.sort(key=lambda x: x['weight_k'])
    return valid_multipliers

# --- UI Layout ---
st.title("✨ Modular Form Eta-Multiplier Finder")
st.markdown("Find $\eta$-multipliers $M(z)$ such that $f(z) \cdot M(z)$ is a holomorphic modular form.")

# Sidebar
with st.sidebar:
    st.header("⚙️ Configuration")
    
    col1, col2 = st.columns(2)
    with col1:
        target_mod = st.number_input("Modulo (t)", min_value=1, value=24)
    with col2:
        target_rem = st.number_input("Remainder (r)", min_value=0, value=16)
        
    level = st.number_input("Search Level (N)", min_value=1, value=48, help="Usually a multiple of the base profile arguments.")
    
    st.markdown("**Base Eta Profile**")
    profile_input = st.text_input("Input (arg:power)", value="1:-1", help="e.g., 1:-1 for 1/eta(z)")
    
    max_exp = st.number_input("Max Exponent", min_value=1, max_value=50, value=10)
    
    st.divider()
    calculate_btn = st.button("🔍 Find Multipliers", use_container_width=True, type="primary")

# Tabs for Main Content
res_tab, hist_tab = st.tabs(["📊 Current Results", "📜 History Log"])

with res_tab:
    if calculate_btn:
        with st.spinner("Searching combinations..."):
            try:
                # Parse input: "1:-1, 4:2" -> {1: -1, 4: 2}
                base_profile = {int(i.split(":")[0].strip()): int(i.split(":")[1].strip()) for i in profile_input.split(",")}
                
                results = find_eta_multiplier(target_mod, target_rem, level, base_profile, max_exp)
                
                if results:
                    # Save to History
                    history_entry = {
                        "params": f"t={target_mod}, r={target_rem}, N={level}",
                        "best_k": results[0]['weight_k'],
                        "top_result": results[0]
                    }
                    st.session_state.history.insert(0, history_entry)
                    if len(st.session_state.history) > 300:
                        st.session_state.history.pop()

                    st.success(f"Found {len(results)} valid multipliers!")
                    
                    for i, res in enumerate(results[:10]):
                        with st.expander(f"Option {i+1}: Weight k={res['weight_k']}, Shift b={res['shift_b']}", expanded=(i==0)):
                            # Build LaTeX
                            parts = []
                            for d, p in res['multiplier_exponents'].items():
                                if p > 0:
                                    term = f"\\eta({d}z)" if p == 1 else f"\\eta^{{{p}}}({d}z)"
                                    parts.append(term)
                            st.latex("".join(parts))
                else:
                    st.warning("No multipliers found. Try increasing Search Level or Max Exponent.")
            except Exception as e:
                st.error(f"Error parsing input: {e}")
    else:
        st.info("Adjust parameters in the sidebar and click search.")

with hist_tab:
    st.header("Search History")
    if not st.session_state.history:
        st.write("No recent searches.")
    else:
        if st.button("Clear All History"):
            st.session_state.history = []
            st.rerun()
            
        for idx, entry in enumerate(st.session_state.history):
            h_col1, h_col2, h_col3 = st.columns([3, 2, 1])
            with h_col1:
                st.markdown(f"**{entry['params']}**")
            with h_col2:
                st.caption(f"Min Weight: {entry['best_k']}")
            with h_col3:
                if st.button("Delete", key=f"del_{idx}"):
                    st.session_state.history.pop(idx)
                    st.rerun()
            st.divider()
