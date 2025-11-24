#!/usr/bin/env python3

# Test what Python's string comparison returns for Metamath variable names
variables = ['x', 'y', 'z', 'a', 'b', 'c', 'ph', 'ps', 'ch', 'th', 'ta', 'et']

print("Python string < comparison:")
for v1 in variables[:6]:
    for v2 in variables[:6]:
        if v1 != v2:
            result = v1 < v2
            print(f"  '{v1}' < '{v2}' = {result}")

print("\nOrdering:")
for v in sorted(variables):
    print(f"  {v}")
