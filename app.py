import streamlit as st
import math
from itertools import product

# --- Paste the gcd, get_divisors, and find_eta_multiplier functions from earlier here ---
def gcd(a, b): return math.gcd(a, b)
def get_divisors(n): return [d for d in range(1, n + 1) if n % d == 0]
# def find_eta_multiplier(...): ... (Keep the exact same function)

# --- Web App UI starts here ---
st.title("Modular Form Eta-Multiplier Finder")
st.write("Find the optimal eta-quotient multiplier to prove partition congruences via Sturm's bound.")

# Create input fields for the user
col1, col2, col3 = st.columns(3)
with col1:
    target_mod = st.number_input("Target Modulo (e.g., 12)", min_value=1, value=12)
with col2:
    target_rem = st.number_input("Target Remainder (e.g., 10)", min_value=0, value=10)
with col3:
    level = st.number_input("Search Level (N)", min_value=1, value=72)

st.write("### Base Eta Profile")
st.write("Enter the eta powers of your generating function (e.g., 6:1 for eta(6z)^1 in numerator, 1:-1 for eta(z)^1 in denominator).")

# A simple text input to let the user define the dictionary
profile_input = st.text_input("Profile (format: argument:power, comma separated)", value="4:1, 6:2, 1:-1, 3:-1, 12:-1")

max_exp = st.slider("Max Exponent to Search", min_value=1, max_value=20, value=10)

if st.button("Find Multiplier"):
    with st.spinner("Calculating... this might take a moment."):
        try:
            # Parse the user's dictionary input
            base_profile = {}
            for item in profile_input.split(","):
                arg, power = item.split(":")
                base_profile[int(arg.strip())] = int(power.strip())
            
            # Run the math function
            results = find_eta_multiplier(target_mod, target_rem, level, base_profile, max_exp)
            
            if results:
                st.success("Optimal Multiplier Found!")
                best = results[0]
                st.metric("Minimal Weight (k)", best['weight_k'])
                st.metric("Shift (b)", best['shift_b'])
                
                st.write("**Multiplier Eta-powers:**")
                for divisor, power in best['multiplier_exponents'].items():
                    if power > 0:
                        st.code(f"eta^{power}({divisor}z)")
            else:
                st.error("No valid multiplier found at this level/max_exponent. Try increasing the level.")
        except Exception as e:
            st.error(f"Error parsing input. Please check your format. Details: {e}")
