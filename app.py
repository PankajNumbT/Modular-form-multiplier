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
    
    # THE FIX: We now allow ALL divisors of the level to be used, not just multiples of the target mod
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
