import streamlit as st
import math
from itertools import product
from fractions import Fraction

# --- Page Configuration ---
st.set_page_config(page_title="Eta-Multiplier Pro", layout="wide")

# --- Optimized Math Utilities ---
def get_divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def constrained_partitions(n, k):
    """
    Returns all lists of n non-negative integers that sum to k.
    This narrows the search space for a fixed weight.
    """
    if n == 1:
        yield [k]
        return
    for i in range(k + 1):
        for p in constrained_partitions(n - 1, k - i):
            yield [i] + p

def get_sturm_bound(k, N):
    index = N
    temp_n = N
    d = 2
    primes = set()
    while d * d <= temp_n:
        if temp_n % d == 0:
            primes.add(d)
            while temp_n % d == 0:
                temp_n //= d
        d += 1
    if temp_n > 1:
        primes.add(temp_n)
    for p in primes:
        index = index * (1 + 1/p)
    return math.ceil((k * index) / 12)

def calculate_cusp_orders(profile, level):
    divs = get_divisors(level)
    return {d: sum((Fraction(math.gcd(d, delta)**2, 24 * delta) * r) 
            for delta, r in profile.items()) for d in divs}

# --- Narrowed Core Logic ---
def find_eta_multipliers(target_mod, target_rem, level, base_profile, max_exp, target_k=None):
    divisors = get_divisors(level)
    allowed_divs = [d for d in divisors if d % target_mod == 0]
    results = []
    
    # Calculate the sum the exponents MUST hit to reach target_k
    # 2k = sum(base_powers) + sum(multiplier_exponents)
    base_weight_2k = sum(base_profile.values())
    
    if target_k is not None:
        required_exp_sum = (2 * target_k) - base_weight_2k
        if required_exp_sum < 0:
            return [] # Impossible to reach weight with non-negative exponents
        # Narrow Search: Only check combinations that sum to required_exp_sum
        search_iterator = constrained_partitions(len(allowed_divs), required_exp_sum)
    else:
        # Broad Search: Standard product
        search_iterator = product(range(max_exp + 1), repeat=len(allowed_divs))

    for exponents in search_iterator:
        current_multiplier = dict(zip(allowed_divs, exponents))
        total_profile = base_profile.copy()
        for d, exp in current_multiplier.items():
            total_profile[d] = total_profile.get(d, 0) + exp
        
        # Calculate Weight
        k = sum(total_profile.values()) / 2
        if not k.is_integer() or k <= 0: continue
        k = int(k)

        # 1. Newman-Ligozat-Wohlfahrt (Mod 24 checks)
        if sum(d * r for d, r in total_profile.items()) % 24 != 0: continue
        if sum((level // d) * r for d, r in total_profile.items()) % 24 != 0: continue
            
        # 2. Cusp Orders (Holomorphicity)
        cusp_orders = calculate_cusp_orders(total_profile, level)
        if any(order < 0 for order in cusp_orders.values()): continue
            
        # 3. Shift b Check
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
    t = st.number_input("Modulo (t)", value=5)
    r = st.number_input("Remainder (r)", value=4)
    N = st.number_input("Level (N)", value=20)
    profile_str = st.text_input("Base Profile (d:r)", value="1:-1, 5:1")
    
    st.divider()
    k_mode = st.radio("Search Optimization", ["Auto (Minimal k)", "Strict (Target k)"])
    target_k = st.number_input("Target k", value=12) if k_mode == "Strict (Target k)" else None
    max_e = st.number_input("Max Exponent (for Auto)", value=10)

    if st.button("🔍 Run Optimized Analysis", type="primary", use_container_width=True):
        try:
            base = {int(x.split(":")[0]): int(x.split(":")[1]) for x in profile_str.split(",")}
            res = find_eta_multipliers(t, r, N, base, max_e, target_k)
            if res:
                st.session_state.current_results = res
            else:
                st.session_state.current_results = "NOT_FOUND"
        except Exception as e:
            st.error(f"Error: {e}")

# --- Display Results ---
if "current_results" in st.session_state:
    if st.session_state.current_results == "NOT_FOUND":
        st.error(f"❌ No valid multipliers exist for the given parameters (k={target_k if target_k else 'any'}).")
    else:
        st.success(f"Found {len(st.session_state.current_results)} candidates.")
        for idx, item in enumerate(st.session_state.current_results[:5]):
            with st.expander(f"Option {idx+1}: k={item['k']}, Sturm={item['sturm']}"):
                st.latex(f"M(z) = " + "".join([f"\\eta^{{{v}}}({k}z)" for k,v in item['multiplier'].items() if v > 0]))
                st.json(item['cusp_orders'])
