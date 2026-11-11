"""python -m speedrunpapi.verifiers.determinism <circuit.r1cs> <report.json>"""
import sys

from .determinism_check import main

if __name__ == "__main__":
    sys.exit(main())
