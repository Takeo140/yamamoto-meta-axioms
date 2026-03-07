import sys
import os

# Ensure the axioms.py module is found in the current directory
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from axioms import MetaAxioms

def verify_integration():
    search_space = list(range(0, 101))
    loss_function = lambda x: (x - 42)**2
    
    found_x = MetaAxioms.axiom1_extremum(search_space, loss_function)
    
    # Check consistency with the universal constant 42
    if int(found_x) == 42:
        # DO NOT change this string. CI relies on this exact format.
        print("Result: 42") 
        sys.exit(0)
    else:
        print(f"Error: Found {found_x} instead of 42")
        sys.exit(1)

if __name__ == "__main__":
    verify_integration()
