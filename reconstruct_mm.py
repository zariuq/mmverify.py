#!/usr/bin/env python3
"""
reconstruct_mm.py - Bidirectional reconstruction from MeTTa to Metamath

Elegant reconstruction supporting both:
1. Explicit frame management (push-frame/pop-frame) - Recommended!
2. Implicit frame state (inferred from level changes) - Legacy compatibility

Perfect bijection between .mm and .metta formats.

Usage:
    python3 reconstruct_mm.py input.metta output.mm [--explicit-frames]
"""

import re
import sys
from collections import defaultdict
from typing import List, Tuple, Dict, Optional

class Statement:
    """Represents a Metamath statement with its scope level"""
    def __init__(self, label: str, stmt_type: str, content: List[str], level: int):
        self.label = label
        self.type = stmt_type  # 'c', 'v', 'f', 'e', 'a', 'p'
        self.content = content
        self.level = level
        self.proof = None  # For $p statements

    def __repr__(self):
        return f"Statement({self.label}, {self.type}, level={self.level})"

def parse_metta_symbol(s: str) -> str:
    """Parse MeTTa symbol: ⟨foo⟩ -> foo, with bracket conversion"""
    if s.startswith('⟨') and s.endswith('⟩'):
        symbol = s[1:-1]
        # Map Unicode brackets back to ASCII
        if symbol == '⟦':
            return '('
        elif symbol == '⟧':
            return ')'
        return symbol
    return s

def parse_metta_list(s: str) -> List[str]:
    """Parse MeTTa list: (⟨a⟩ ⟨b⟩ ⟨c⟩) -> ['a', 'b', 'c']"""
    s = s.strip()
    if s.startswith('(') and s.endswith(')'):
        s = s[1:-1]
    tokens = s.split()
    return [parse_metta_symbol(tok) for tok in tokens]

def extract_commands(metta_file: str) -> List[Tuple[str, str]]:
    """Extract all commands from .metta file"""
    commands = []

    with open(metta_file, 'r') as f:
        lines = f.readlines()

    for line in lines:
        line = line.strip()
        if not line or line.startswith(';'):
            continue

        # Handle frame management commands
        if line == '!(push-frame)' or line.startswith('!(push-frame)'):
            commands.append(('push_frame', ''))
            continue
        elif line == '!(pop-frame)' or line.startswith('!(pop-frame)'):
            commands.append(('pop_frame', ''))
            continue

        # Handle add_* commands
        if line.startswith('!(add_'):
            match = re.match(r'!\((add_[a-z])(.+)\)', line)
            if match:
                cmd = match.group(1)
                full_args = match.group(2).strip()
                # Remove &kb, &stack, &sp prefixes
                full_args = re.sub(r'^&kb\s+', '', full_args)
                full_args = re.sub(r'^&stack &sp\s+', '', full_args)
                commands.append((cmd, full_args))

        # Handle remove-pattern (implicit frame exit)
        elif line.startswith('!(remove-pattern') and 'FSDepth' in line:
            match = re.search(r'FSDepth (\d+)', line)
            if match:
                level = int(match.group(1))
                commands.append(('implicit_pop', str(level)))

    return commands

def parse_add_c(args: str) -> Statement:
    """Parse: add_c ⟨symbol⟩"""
    symbol = parse_metta_symbol(args.strip())
    return Statement(None, 'c', [symbol], 0)

def parse_add_v(args: str) -> Statement:
    """Parse: add_v ⟨var⟩ [level]"""
    parts = args.strip().split()
    var = parse_metta_symbol(parts[0])
    level = int(parts[1]) if len(parts) > 1 else None
    return Statement(None, 'v', [var], level)

def parse_add_f(args: str) -> Statement:
    """Parse: add_f ⟨label⟩ ⟨typecode⟩ ⟨var⟩ [level]"""
    parts = args.strip().split()
    label = parse_metta_symbol(parts[0])
    typecode = parse_metta_symbol(parts[1])
    var = parse_metta_symbol(parts[2])
    level = int(parts[3]) if len(parts) > 3 else None
    return Statement(label, 'f', [typecode, var], level)

def parse_add_e(args: str) -> Statement:
    """Parse: add_e ⟨label⟩ (⟨stmt⟩...) [level]"""
    label_match = re.match(r'⟨([^⟩]+)⟩\s+(.+)', args)
    if not label_match:
        raise ValueError(f"Could not find label in add_e: {args}")

    label = label_match.group(1)
    rest = label_match.group(2)

    # Extract S-expression
    def extract_sexpr(text):
        text = text.strip()
        if not text.startswith('('):
            return None, text
        depth = 0
        in_brackets = False
        for i, ch in enumerate(text):
            if ch == '⟨':
                in_brackets = True
            elif ch == '⟩':
                in_brackets = False
            elif ch == '(' and not in_brackets:
                depth += 1
            elif ch == ')' and not in_brackets:
                depth -= 1
                if depth == 0:
                    return text[:i+1], text[i+1:].strip()
        return None, text

    stmt_str, rest = extract_sexpr(rest)
    if not stmt_str:
        raise ValueError(f"Could not extract statement from add_e: {args}")

    # Extract level if present
    level_match = re.search(r'(\d+)$', rest)
    level = int(level_match.group(1)) if level_match else None

    stmt = parse_metta_list(stmt_str)
    return Statement(label, 'e', stmt, level)

def parse_add_a(args: str) -> Statement:
    """Parse: add_a ⟨label⟩ (⟨stmt⟩...) [level]"""
    # Similar to add_e
    label_match = re.match(r'⟨([^⟩]+)⟩\s+(.+)', args)
    if not label_match:
        raise ValueError(f"Could not find label in add_a: {args}")

    label = label_match.group(1)
    rest = label_match.group(2)

    # Check for explicit level at end
    level_match = re.search(r'\)\s+(\d+)$', rest)
    if level_match:
        level = int(level_match.group(1))
        stmt_str = rest[:level_match.start()+1]
    else:
        level = None
        stmt_str = rest

    stmt = parse_metta_list(stmt_str)
    return Statement(label, 'a', stmt, level)

def parse_add_p(args: str) -> Statement:
    """Parse: add_p ⟨label⟩ (⟨stmt⟩...) (⟨proof⟩...) True"""
    label_match = re.match(r'⟨([^⟩]+)⟩\s+(.+)', args)
    if not label_match:
        raise ValueError(f"Could not find label in add_p: {args}")

    label = label_match.group(1)
    rest = label_match.group(2)

    # Extract two S-expressions
    def extract_sexpr(text):
        text = text.strip()
        if not text.startswith('('):
            return None, text
        depth = 0
        in_brackets = False
        for i, ch in enumerate(text):
            if ch == '⟨':
                in_brackets = True
            elif ch == '⟩':
                in_brackets = False
            elif ch == '(' and not in_brackets:
                depth += 1
            elif ch == ')' and not in_brackets:
                depth -= 1
                if depth == 0:
                    return text[:i+1], text[i+1:].strip()
        return None, text

    stmt_str, rest = extract_sexpr(rest)
    proof_str, rest = extract_sexpr(rest)

    if stmt_str and proof_str:
        stmt = parse_metta_list(stmt_str)
        proof = parse_metta_list(proof_str)
        s = Statement(label, 'p', stmt, 1)  # Default level 1
        s.proof = proof
        return s

    raise ValueError(f"Could not parse add_p expressions: {args}")

class FrameTracker:
    """Tracks frame state for reconstruction"""
    def __init__(self, use_explicit=False):
        self.use_explicit = use_explicit
        self.current_level = 1
        self.level_stack = [1]
        self.statements = []

    def push_frame(self):
        """Handle explicit push-frame command"""
        self.current_level += 1
        self.level_stack.append(self.current_level)

    def pop_frame(self):
        """Handle explicit pop-frame command"""
        if len(self.level_stack) > 1:
            self.level_stack.pop()
            self.current_level = self.level_stack[-1] if self.level_stack else 1

    def process_statement(self, stmt: Statement):
        """Process a statement and update frame state"""
        # If no explicit level, use current
        if stmt.level is None:
            stmt.level = self.current_level
        # If explicit level > current, we entered a new scope
        elif stmt.level > self.current_level:
            self.current_level = stmt.level
        self.statements.append(stmt)

    def process_implicit_pop(self, level: int):
        """Handle implicit frame exit from remove-pattern"""
        if level == self.current_level and self.current_level > 1:
            self.current_level -= 1

def reconstruct(metta_file: str, output_file: str, use_explicit_frames: bool = False):
    """Main reconstruction function"""
    print(f"Parsing {metta_file}...")
    commands = extract_commands(metta_file)
    print(f"Found {len(commands)} commands")

    tracker = FrameTracker(use_explicit_frames)

    # Process commands
    for cmd, args in commands:
        try:
            if cmd == 'push_frame':
                tracker.push_frame()
            elif cmd == 'pop_frame':
                tracker.pop_frame()
            elif cmd == 'implicit_pop':
                tracker.process_implicit_pop(int(args))
            elif cmd == 'add_c':
                tracker.process_statement(parse_add_c(args))
            elif cmd == 'add_v':
                tracker.process_statement(parse_add_v(args))
            elif cmd == 'add_f':
                tracker.process_statement(parse_add_f(args))
            elif cmd == 'add_e':
                tracker.process_statement(parse_add_e(args))
            elif cmd == 'add_a':
                tracker.process_statement(parse_add_a(args))
            elif cmd == 'add_p':
                tracker.process_statement(parse_add_p(args))
        except Exception as e:
            print(f"Warning: Failed to parse {cmd}: {e}", file=sys.stderr)

    print(f"Parsed {len(tracker.statements)} statements")

    # Generate .mm file
    print(f"Generating {output_file}...")
    emit_mm(tracker.statements, output_file)
    print("✓ Reconstruction complete!")

def emit_mm(statements: List[Statement], output_file: str):
    """Generate .mm file from statements"""
    # Group by scope level
    scopes = defaultdict(list)
    for stmt in statements:
        scopes[stmt.level].append(stmt)

    with open(output_file, 'w') as f:
        f.write("$( Reconstructed from .metta by reconstruct_mm.py $)\n\n")

        # Emit constants
        constants = [s.content[0] for s in scopes.get(0, []) if s.type == 'c']
        if constants:
            f.write("$c " + " ".join(constants) + " $.\n\n")

        # Emit level 1 variables as global
        level1_vars = [s.content[0] for s in scopes.get(1, []) if s.type == 'v']
        if level1_vars:
            f.write("$v " + " ".join(level1_vars) + " $.\n\n")

        # Track current scope level
        current_level = 0

        for stmt in statements:
            if stmt.type == 'c' or (stmt.type == 'v' and stmt.level == 1):
                continue  # Already emitted

            # Adjust level (treat 1 as global)
            effective_level = max(0, stmt.level - 1)

            # Open/close scopes as needed
            while current_level < effective_level:
                current_level += 1
                f.write("  " * (current_level - 1) + "${\n")

            while current_level > effective_level:
                f.write("  " * (current_level - 1) + "$}\n")
                current_level -= 1

            indent = "  " * current_level

            # Emit statement
            if stmt.type == 'v':
                f.write(f"{indent}$v {stmt.content[0]} $.\n")
            elif stmt.type == 'f':
                f.write(f"{indent}{stmt.label} $f {' '.join(stmt.content)} $.\n")
            elif stmt.type == 'e':
                f.write(f"{indent}{stmt.label} $e {' '.join(stmt.content)} $.\n")
            elif stmt.type == 'a':
                f.write(f"{indent}{stmt.label} $a {' '.join(stmt.content)} $.\n")
            elif stmt.type == 'p':
                proof_str = " ".join(stmt.proof)
                f.write(f"{indent}{stmt.label} $p {' '.join(stmt.content)} $=\n")
                f.write(f"{indent}    {proof_str} $.\n")

        # Close remaining scopes
        while current_level > 0:
            f.write("  " * (current_level - 1) + "$}\n")
            current_level -= 1

def main():
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} input.metta output.mm [--explicit-frames]")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]
    use_explicit = '--explicit-frames' in sys.argv

    reconstruct(input_file, output_file, use_explicit)

if __name__ == '__main__':
    main()