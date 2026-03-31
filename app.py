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

def format_latex_frac(frac):
    if frac.denominator == 1:
        return f"{frac.numerator}"
    return f"\\dfrac{{{frac.numerator}}}{{{frac.denominator}}}"

# --- LaTeX Generator ---
def generate_latex_export(t, r, N, base_profile, item):
    base_parts = []
    for d, p in base_profile.items():
        if p == 1: base_parts.append(f"\\eta({d}z)")
        elif p != 0: base_parts.append(f"\\eta^{{{p}}}({d}z)")
    base_lat = "".join(base_parts)

    mult_parts = []
    for d, p in item['multiplier'].items():
        if p == 1: mult_parts.append(f"\\eta({d}z)")
        elif p > 1: mult_parts.append(f"\\eta^{{{p}}}({d}z)")
    mult_lat = "".join(mult_parts) if mult_parts else "1"

    latex_code = f"""% --- Auto-Generated Modular Form Data ---
\\begin{{align*}}
    \\text{{Level }} (N) &= {N} \\\\
    \\text{{Target}} &\\equiv {r} \\pmod{{{t}}} \\\\
    \\text{{Base Quotient}} &= {base_lat} \\\\
    \\text{{Multiplier }} M(z) &= {mult_lat} \\\\
    \\text{{Total Weight }} (k) &= {item['k']} \\\\
    \\text{{Total Shift }} (b) &= {item['total_b']} \\\\
    \\text{{Sturm Bound }} (S) &= {item['sturm']}
\\end{{align*}}

\\begin{{table}}[htbp]
    \\centering
    \\renewcommand{{\\arraystretch}}{{1.5}}
    \\begin{{tabular}}{{|c|c|}}
    \\hline
    \\textbf{{Cusp ($\\frac{{1}}{{d}}$)}} & \\textbf{{Order ($ord(f, c)$)}} \\\\ \\hline
"""
    for c, val in item['cusp_orders'].items():
        frac_str = f"\\frac{{{val.numerator}}}{{{val.denominator}}}" if val.denominator != 1 else f"{val.numerator}"
        latex_code += f"    $\\frac{{1}}{{{c}}}$ & ${frac_str}$ \\\\ \\hline\n"

    latex_code += f"""    \\end{{tabular}}
    \\caption{{Orders of vanishing at the cusps of $\\Gamma_0({N})$}}
\\end{{table}}
"""
    return latex_code

# --- OPTIMIZED CORE LOGIC ---
# Added st.cache_data so repeated runs are instant
@st.cache_data(show_spinner=False)
def find_eta_multipliers(target_mod, target_rem, level, base_profile, max_exp, search_mode="Standard", target_k=None, targeted_divs=None):
    divisors = get_divisors(level)
    
    if search_mode == "Deep Search (Targeted)":
        allowed_divs = tuple(targeted_divs) if targeted_divs else tuple(divisors)
    else:
        allowed_divs = tuple(divisors)

    results = []
    base_weight_2k = sum(base_profile.values())
    
    # ⚡ SPEED BOOST: Pre-compute the Cusp Matrix outside the loop
    all_deltas = set(base_profile.keys()).union(set(allowed_divs))
    cusp_matrix = {d: {delta: Fraction(math.gcd(d, delta)**2, 24 * delta) for delta in all_deltas} for d in divisors}
    
    if search_mode == "Standard (All Divisors)" and target_k is not None:
        required_exp_sum = (2 * target_k) - base_weight_2k
        if required_exp_sum < 0: return []
        search_iterator = constrained_partitions(len(allowed_divs), required_exp_sum)
    else:
        search_iterator = product(range(max_exp + 1), repeat=len(allowed_divs))

    for exponents in search_iterator:
        current_multiplier = dict(zip(allowed_divs, exponents))
        
        # Fast profile merge
        total_profile = base_profile.copy()
        for d, exp in current_multiplier.items():
            if exp > 0:
                total_profile[d] = total_profile.get(d, 0) + exp
        
        # 1. Check Weight
        k_val = sum(total_profile.values()) / 2
        if not k_val.is_integer() or k_val <= 0: continue
        k = int(k_val)

        # 2. Check Mod 24 Conditions
        total_b_num = sum(d * r for d, r in total_profile.items())
        if total_b_num % 24 != 0: continue
        
        sum_Ndr = sum((level // d) * r for d, r in total_profile.items())
        if sum_Ndr % 24 != 0: continue
            
        # 3. ⚡ FAST Cusp Holomorphicity Check
        is_holomorphic = True
        cusp_orders = {}
        for d in divisors:
            # Look up pre-computed fractions instead of recalculating
            order = sum(cusp_matrix[d][delta] * r for delta, r in total_profile.items())
            if order < 0:
                is_holomorphic = False
                break # Exit instantly if any cusp goes negative
            cusp_orders[d] = order
            
        if not is_holomorphic: continue
            
        # 4. Check Shift Congruence Alignment
        total_b = total_b_num // 24
        if (total_b + target_rem) % target_mod == 0:
            results.append({
                'multiplier': current_multiplier, 'k': k, 'total_b': total_b,
                'cusp_orders': cusp_orders, 'sturm': get_sturm_bound(k, level)
            })
            
    return sorted(results, key=lambda x: x['k'])

# --- UI Layout ---
st.title("🛡️ Modular Form Eta-Multiplier Finder")

with st.sidebar:
    st.header("⚙️ Configuration")
    t = st.number_input("Modulo (t)", value=43)
    r = st.number_input("Remainder (r)", value=12)
    N = st.number_input("Level (N)", value=4)
    
    st.divider()
    st.subheader("Base Eta Quotient")
    
    if 'input_data' not in st.session_state:
        st.session_state.input_data = pd.DataFrame([
            {"Divisor (d)": 1, "Power (r)": -1},
            {"Divisor (d)": 2, "Power (r)": -36}
        ])

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
    st.subheader("Search Strategy")
    search_mode = st.radio("Mode", ["Standard (All Divisors)", "Deep Search (Targeted)"], label_visibility="collapsed")
    
    target_k = None
    targeted_divs = []
    
    if search_mode == "Standard (All Divisors)":
        k_mode = st.radio("Optimization", ["Auto (Minimal k)", "Strict (Target k)"])
        if k_mode == "Strict (Target k)":
            target_k = st.number_input("Target k", value=12)
        max_e = st.number_input("Max Exponent", value=10)
    else:
        st.caption("Isolate specific divisors to search massive exponents instantly.")
        all_divs = get_divisors(N)
        targeted_divs = st.multiselect("Select Divisors for Multiplier", all_divs, default=[1])
        max_e = st.number_input("Max Exponent Limit", value=1000)

    if st.button("🔍 Run Analysis", type="primary", use_container_width=True):
        try:
            clean_df = edited_df.replace('', pd.NA).dropna(subset=["Divisor (d)", "Power (r)"])
            clean_df = clean_df[clean_df["Divisor (d)"] > 0]
            
            if clean_df.empty:
                st.error("Please provide at least one valid Divisor and Power.")
            else:
                base = dict(zip(clean_df["Divisor (d)"].astype(int), clean_df["Power (r)"].astype(int)))
                
                # Visual Spinner added here
                with st.spinner("Crunching the numbers... Please wait."):
                    res = find_eta_multipliers(t, r, N, base, max_e, search_mode, target_k, targeted_divs)
                
                st.session_state.current_results = res if res else "NOT_FOUND"
                st.session_state.current_params = {'t': t, 'r': r, 'N': N, 'base': base}
        except Exception as e:
            st.error(f"Analysis failed. Details: {e}")

# --- Display Results ---
if "current_results" in st.session_state:
    if st.session_state.current_results == "NOT_FOUND":
        st.error("❌ No valid multipliers exist for these parameters.")
    else:
        st.success(f"Found {len(st.session_state.current_results)} candidates.")
        
        p = st.session_state.current_params
        
        for idx, item in enumerate(st.session_state.current_results[:10]):
            with st.expander(f"Candidate {idx+1} | Total Weight k = {item['k']} | Sturm = {item['sturm']}", expanded=(idx==0)):
                
                tab1, tab2 = st.tabs(["📊 Visual Dashboard", "📝 Copy LaTeX Export"])
                
                with tab1:
                    col1, col2 = st.columns([1, 1.2])
                    with col1:
                        st.markdown("**Found Multiplier**")
                        mult_lat = "".join([f"\\eta^{{{v}}}({k}z)" if v > 1 else f"\\eta({k}z)" 
                                          for k, v in item['multiplier'].items() if v > 0])
                        st.latex(f"M(z) = {mult_lat}")
                        st.metric("Total Shift (b)", item['total_b'])
                    
                    with col2:
                        st.markdown("**Total Orders at Cusps ($ord(f, c)$)**")
                        md_table = "| Cusp ($1/d$) | Vanishing Order |\n| :---: | :---: |\n"
                        for c, val in item['cusp_orders'].items():
                            md_table += f"| $1/{c}$ | ${format_latex_frac(val)}$ |\n"
                        st.markdown(md_table)
                
                with tab2:
                    st.markdown("Hover over the code block below and click the **Copy** icon in the top right to copy the formatted LaTeX.")
                    latex_string = generate_latex_export(p['t'], p['r'], p['N'], p['base'], item)
                    st.code(latex_string, language="latex")
