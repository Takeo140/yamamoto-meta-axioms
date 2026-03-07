import sys
import os

# Add the current directory to sys.path to ensure 'axioms.py' is found
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

try:
    from axioms import MetaAxioms
except ImportError:
    print("Error: axioms.py not found in the current directory.")
    sys.exit(1)

def verify_integration():
    # ... (rest of your logic)
    search_space = list(range(0, 101))
    loss_function = lambda x: (x - 42)**2
    
    found_x = MetaAxioms.axiom1_extremum(search_space, loss_function)
    is_valid = MetaAxioms.axiom2_boundary_check(found_x, search_space)
    consistency_error = MetaAxioms.axiom3_consistency(found_x, 42)
    
    if is_valid and consistency_error == 0:
        print("-------------------------------")
        print("CI STATUS: [GREEN]")
        print("Logical Consistency: SUCCESS")
        print(f"Result: 42")
        print("-------------------------------")
    else:
        sys.exit(1)

if __name__ == "__main__":
    verify_integration()
