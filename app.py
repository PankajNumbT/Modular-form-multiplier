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

# --- CRASH-PROOF LaTeX Generator ---
def generate_latex_export(t, r, N, base_profile, item):
    """Generates a formatted LaTeX string using lists to prevent f-string copy errors."""
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

    lines = [
        "% --- Auto-Generated Modular Form Data ---",
        "\\begin{align*}",
        f"    \\text{{Level }} (N) &= {N} \\\\",
        f"    \\text{{Target}} &\\equiv {r} \\pmod{{{t}}} \\\\",
        f"    \\text{{Base Quotient}} &= {base_lat} \\\\",
        f"    \\text{{Multiplier }} M(z) &= {mult_lat} \\\\",
        f"    \\text{{Total Weight }} (k) &= {item['k']} \\\\",
        f"    \\text{{Total Shift }} (b) &= {item['total_b']} \\\\",
        f"    \\text{{Sturm Bound }} (S) &= {item['sturm']}",
        "\\end{align*}",
        "",
        "\\begin{table}[htbp]",
        "    \\centering",
        "    \\renewcommand{\\arraystretch}{1.5}",
        "    \\begin{tabular}{|c|c|}",
        "    \\hline",
        "    \\textbf{Cusp ($\\frac{1}{d}$)} & \\textbf{Order ($ord(f, c)$)} \\\\ \\hline"
    ]

    for c, val in item['cusp_orders'].items():
        frac_str = f"\\frac{{{val.numerator}}}{{{val.denominator}}}" if val.denominator != 1 else f"{val.numerator}"
        lines.append(f"    $\\frac{{1}}{{{c}}}$ & ${frac_str}$ \\\\ \\hline")

    lines.extend([
        "    \\end{tabular}",
        f"    \\caption{{Orders of vanishing at the cusps of $\\Gamma_0({N})$}}",
        "\\end{table}"
    ])

    return "\n".join(lines)

# --- OPTIMIZED CORE LOGIC ---
@st.cache_data(show_spinner=False)
def find_eta_multipliers(target_mod, target_rem, level, base_profile_tuple, min_exp, max_exp, search_mode="Standard", target_k=None, targeted_divs_tuple=None, limit_n=None, limit_sturm=None, prevent_cancel=False):
    # Convert tuples back to dictionary/list inside the function so Streamlit's cache doesn't crash
    base_profile = dict(base_profile_tuple)
    targeted_divs = list(targeted_divs_tuple) if targeted_divs_tuple else None
    
    divisors = get_divisors(level)
    
    # Apply targeted divisors if in Deep Search mode
    if search_mode == "Deep Search (Targeted)":
        allowed_divs = tuple(targeted_divs) if targeted_divs else tuple(divisors)
    else:
        allowed_divs = tuple(divisors)

    results = []
    base_weight_2k = sum(base_profile.values())
    
    # Pre-compute the Cusp Matrix outside the loop for speed
    all_deltas = set(base_profile.keys()).union(set(allowed_divs))
    cusp_matrix = {d: {delta: Fraction(math.gcd(d, delta)**2, 24 * delta) for delta in all_deltas} for d in divisors}
    
    # SEARCH SPACE: Support for asymmetric manual bounds
    if search_mode == "Standard (All Divisors)" and target_k is not None:
        required_exp_sum = (2 * target_k) - base_weight_2k
        if required_exp_sum < 0: return []
        search_iterator = constrained_partitions(len(allowed_divs), required_exp_sum)
    else:
        # Searches from min_exp to max_exp exactly as requested
        search_iterator = product(range(min_exp, max_exp + 1), repeat=len(allowed_divs))

    for exponents in search_iterator:
        current_multiplier = dict(zip(allowed_divs, exponents))
        
        # Fast profile merge
        total_profile = base_profile.copy()
        for d, exp in current_multiplier.items():
            if exp != 0:
                total_profile[d] = total_profile.get(d, 0) + exp
                
        # --- CANCELLATION PREVENTION LOGIC ---
        if prevent_cancel:
            # If any divisor from the base perfectly equals 0 in the total, skip it
            if any(total_profile.get(d, 0) == 0 for d in base_profile.keys()):
                continue
        
        # 1. Check Weight
        k_val = sum(total_profile.values()) / 2
        if not k_val.is_integer() or k_val <= 0: continue
        k = int(k_val)

        # 2. Check Mod 24 Conditions
        total_b_num = sum(d * r for d, r in total_profile.items())
        if total_b_num % 24 != 0: continue
        
        sum_Ndr = sum((level // d) * r for d, r in total_profile.items())
        if sum_Ndr % 24 != 0: continue
            
        # 3. FAST Cusp Holomorphicity Check
        is_holomorphic = True
        cusp_orders = {}
        for d in divisors:
            order = sum(cusp_matrix[d][delta] * r for delta, r in total_profile.items())
            if order < 0:
                is_holomorphic = False
                break
            cusp_orders[d] = order
            
        if not is_holomorphic: continue
            
        # 4. Check Shift Congruence Alignment
        total_b = total_b_num // 24
        if (total_b + target_rem) % target_mod == 0:
            
            # --- EARLY STOPPING LOGIC ---
            sturm = get_sturm_bound(k, level)
            
            # If a max sturm bound is set and this exceeds it, skip it entirely
            if limit_sturm is not None and sturm > limit_sturm:
                continue
            
            results.append({
                'multiplier': current_multiplier, 'k': k, 'total_b': total_b,
                'cusp_orders': cusp_orders, 'sturm': sturm
            })
            
            # If we hit the requested number of results, abort the loop and return instantly
            if limit_n is not None and len(results) >= limit_n:
                break
            
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
    st.caption("Defaults set to $1/(f_1 f_2^{36})$")
    
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
        k_mode = st.radio("Optimization", ["Auto (Minimal k, allows negatives)", "Strict (Target k, positive only)"])
        if k_mode == "Strict (Target k, positive only)":
            target_k = st.number_input("Target k", value=12)
            min_e = 0
            max_e = st.number_input("Max Exponent Bound", value=10)
        else:
            col1, col2 = st.columns(2)
            with col1:
                min_e = st.number_input("Min Exponent", value=-2)
            with col2:
                max_e = st.number_input("Max Exponent", value=10)
    else:
        st.caption("Isolate specific divisors to search massive exponents instantly.")
        all_divs = get_divisors(N)
        targeted_divs = st.multiselect("Select Divisors for Multiplier", all_divs, default=[1])
        
        col1, col2 = st.columns(2)
        with col1:
            min_e = st.number_input("Min Exponent", value=0)
        with col2:
            max_e = st.number_input("Max Exponent", value=1000)

    # --- ADVANCED FILTERS & LIMITS ---
    st.divider()
    st.subheader("Advanced Filters & Limits")
    
    # Toggle to prevent cancellation
    prevent_cancel = st.checkbox("Strict Preservation (Forbid Cancellation)", value=False, help="Ensures the multiplier does not completely cancel out any term from the base quotient.")
    
    # Toggle for Early Stopping
    use_early_stop = st.checkbox("Enable Early Stopping (Speed Optimization)", value=False, help="Stop the search automatically once enough valid multipliers are found.")
    
    limit_n = None
    limit_sturm = None
    
    if use_early_stop:
        col3, col4 = st.columns(2)
        with col3:
            limit_n = st.number_input("Stop after finding N results:", value=10, min_value=1)
        with col4:
            limit_sturm = st.number_input("Max Sturm Bound Limit:", value=250, min_value=1)

    if st.button("🔍 Run Analysis", type="primary", use_container_width=True):
        try:
            clean_df = edited_df.replace('', pd.NA).dropna(subset=["Divisor (d)", "Power (r)"])
            clean_df = clean_df[clean_df["Divisor (d)"] > 0]
            
            if min_e > max_e:
                st.error("Min Exponent cannot be strictly greater than Max Exponent.")
            elif clean_df.empty:
                st.error("Please provide at least one valid Divisor and Power.")
            else:
                base = dict(zip(clean_df["Divisor (d)"].astype(int), clean_df["Power (r)"].astype(int)))
                
                with st.spinner("Crunching the numbers... Please wait."):
                    res = find_eta_multipliers(
                        t, r, N, 
                        tuple(base.items()), 
                        min_e, max_e, search_mode, target_k, 
                        tuple(targeted_divs),
                        limit_n, limit_sturm, prevent_cancel
                    )
                
                st.session_state.current_results = res if res else "NOT_FOUND"
                st.session_state.current_params = {'t': t, 'r': r, 'N': N, 'base': base}
                
                # Show a warning message if we hit the early stop limit
                if limit_n is not None and len(res) >= limit_n:
                    st.toast(f"✅ Search stopped early after finding {limit_n} valid results!")

        except Exception as e:
            st.error(f"Analysis failed. Details: {e}")

    # --- DEVELOPER CREDIT FOOTER ---
    st.divider()
    st.markdown(
        """
        <div style='text-align: center; color: gray; font-size: 0.85em;'>
            Developed by <b>[Pankaj Gogoi]</b><br>
            <i>[Tezpur University, gopankajgo07@gmail.com]</i>
        </div>
        """, 
        unsafe_allow_html=True
    )

# --- Display Results ---
if "current_results" in st.session_state:
    if st.session_state.current_results == "NOT_FOUND":
        st.error("❌ No valid multipliers exist for these parameters.")
    else:
        st.success(f"Found {len(st.session_state.current_results)} candidates.")
        
        p = st.session_state.current_params
        
        # We display all results found (up to the limit_n if early stop was used)
        for idx, item in enumerate(st.session_state.current_results):
            with st.expander(f"Candidate {idx+1} | Total Weight k = {item['k']} | Sturm = {item['sturm']}", expanded=(idx==0)):
                
                tab1, tab2 = st.tabs(["📊 Visual Dashboard", "📝 Copy LaTeX Export"])
                
                with tab1:
                    col1, col2 = st.columns([1, 1.2])
                    with col1:
                        st.markdown("**Found Multiplier**")
                        mult_lat = "".join([f"\\eta^{{{v}}}({k}z)" if v not in [0, 1] else (f"\\eta({k}z)" if v == 1 else "") 
                                          for k, v in item['multiplier'].items() if v != 0])
                        if not mult_lat: mult_lat = "1"
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
