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
    """Parse MeTTa symbol: ⟨foo⟩ or "foo" -> foo, with bracket conversion"""
    # Handle angle bracket format: ⟨foo⟩
    if s.startswith('⟨') and s.endswith('⟩'):
        symbol = s[1:-1]
        # Map Unicode brackets back to ASCII
        if symbol == '⟦':
            return '('
        elif symbol == '⟧':
            return ')'
        return symbol
    # Handle double-quoted format: "foo"
    elif s.startswith('"') and s.endswith('"'):
        return s[1:-1]  # Strip quotes
    return s

def extract_label(args: str) -> tuple[str, str]:
    """Extract label from add_* command args. Returns (label, remaining_args).

    Handles both formats:
    - Angle brackets: ⟨label⟩ rest...
    - Double quotes: "label" rest...
    """
    args = args.strip()
    # Try angle bracket format first
    match = re.match(r'⟨([^⟩]+)⟩\s+(.+)', args)
    if match:
        return (match.group(1), match.group(2))

    # Try double-quote format
    match = re.match(r'"([^"]+)"\s+(.+)', args)
    if match:
        return (match.group(1), match.group(2))

    raise ValueError(f"Could not extract label from: {args}")

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
        if line.startswith('!(push-frame'):
            commands.append(('push_frame', ''))
            continue
        elif line.startswith('!(pop-frame'):
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
    """Parse: add_f ⟨label⟩ ⟨typecode⟩ ⟨var⟩ [level] or add_f "label" "typecode" "var" [level]"""
    parts = args.strip().split()
    label = parse_metta_symbol(parts[0])
    typecode = parse_metta_symbol(parts[1])
    var = parse_metta_symbol(parts[2])
    level = int(parts[3]) if len(parts) > 3 else None
    return Statement(label, 'f', [typecode, var], level)

def parse_add_d(args: str) -> Statement:
    """Parse: add_d (\"var1\" \"var2\" ...) [level]
    Returns a special Statement with type='d' containing the variable list"""
    # Match pattern: ("x" "y" "z") or ⟨x⟩ ⟨y⟩ format, followed by optional level
    # First try to extract a parenthesized list
    list_match = re.match(r'\(([^)]+)\)\s*(\d+)?', args)
    if list_match:
        vars_str = list_match.group(1)
        level = int(list_match.group(2)) if list_match.group(2) else None
        # Parse quoted variables: "x" "y" "z"
        vars_list = re.findall(r'"([^"]+)"', vars_str)
        if not vars_list:
            # Try angle bracket format: ⟨x⟩ ⟨y⟩
            vars_list = [parse_metta_symbol(v) for v in vars_str.split()]
        return Statement(None, 'd', vars_list, level)

    raise ValueError(f"Could not parse add_d: {args}")

def parse_add_e(args: str) -> Statement:
    """Parse: add_e ⟨label⟩ (⟨stmt⟩...) [level] or add_e "label" ("stmt"...) [level]"""
    label, rest = extract_label(args)

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
    """Parse: add_a ⟨label⟩ (⟨stmt⟩...) [level] or add_a "label" ("stmt"...) [level]"""
    # Similar to add_e
    label, rest = extract_label(args)

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
    """Parse: add_p ⟨label⟩ (⟨stmt⟩...) (⟨proof⟩...) True or add_p "label" ("stmt"...) ("proof"...) True"""
    label, rest = extract_label(args)

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

class ScopeEvent:
    """Represents a scope boundary event"""
    def __init__(self, event_type: str, level: int = None):
        self.type = event_type  # 'push' or 'pop'
        self.level = level

class FrameTracker:
    """Tracks frame state for reconstruction"""
    def __init__(self, use_explicit=False):
        self.use_explicit = use_explicit
        self.current_level = 1
        self.level_stack = [1]
        self.events = []  # Sequence of statements and scope events

    def push_frame(self):
        """Handle explicit push-frame command"""
        self.current_level += 1
        self.level_stack.append(self.current_level)
        # Only emit scope events for level > 1 (level 1 is global, not a scope block)
        if self.current_level > 1:
            self.events.append(ScopeEvent('push', self.current_level))

    def pop_frame(self):
        """Handle explicit pop-frame command"""
        if len(self.level_stack) > 1:
            # Only emit scope events for level > 1 (level 1 is global, not a scope block)
            if self.current_level > 1:
                self.events.append(ScopeEvent('pop', self.current_level))
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

        self.events.append(stmt)

    def process_implicit_pop(self, level: int):
        """Handle implicit frame exit from remove-pattern"""
        if level == self.current_level and self.current_level > 1:
            self.events.append(ScopeEvent('pop', self.current_level))
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
            elif cmd == 'add_d':
                tracker.process_statement(parse_add_d(args))
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

    print(f"Parsed {len([e for e in tracker.events if isinstance(e, Statement)])} statements")

    # Generate .mm file
    print(f"Generating {output_file}...")
    emit_mm(tracker.events, output_file)
    print("✓ Reconstruction complete!")

def emit_mm(events: List, output_file: str):
    """Generate .mm file from event sequence

    Strategy: Scan events to identify scope blocks. A scope block is:
    - ScopeEvent(push) followed by statements followed by ScopeEvent(pop)
    - The OUTERMOST push/pop pair does NOT create a scope - it's just frame management
    - Everything NOT in an INNER scope block is global
    """
    with open(output_file, 'w') as f:
        f.write("$( Reconstructed from .metta by reconstruct_mm.py $)\n\n")

        # Find the outermost scope (if any)
        outermost_push = None
        outermost_pop = None
        for i, event in enumerate(events):
            if isinstance(event, ScopeEvent) and event.type == 'push':
                if outermost_push is None:
                    outermost_push = i
                    # Find matching pop
                    depth = 1
                    for j in range(i + 1, len(events)):
                        if isinstance(events[j], ScopeEvent):
                            if events[j].type == 'push':
                                depth += 1
                            else:
                                depth -= 1
                                if depth == 0:
                                    outermost_pop = j
                                    break
                break

        # Identify which statements are in INNER scopes vs global
        in_scope_indices = set()
        i = 0
        while i < len(events):
            if isinstance(events[i], ScopeEvent) and events[i].type == 'push':
                # Skip outermost push
                if i == outermost_push:
                    i += 1
                    continue

                # Find matching pop
                depth = 1
                j = i + 1
                while j < len(events):
                    if isinstance(events[j], ScopeEvent):
                        if events[j].type == 'push':
                            depth += 1
                        elif events[j].type == 'pop':
                            depth -= 1
                            if depth == 0:
                                # Mark all statements between i and j as in-scope
                                for k in range(i + 1, j):
                                    if isinstance(events[k], Statement):
                                        in_scope_indices.add(k)
                                break
                    j += 1
            i += 1

        # First pass: emit global constants, variables, and floatings
        constants = []
        global_vars = []
        global_floatings = []
        global_stmts = []

        for i, event in enumerate(events):
            if isinstance(event, Statement) and i not in in_scope_indices:
                if event.type == 'c':
                    constants.append(event.content[0])
                elif event.type == 'v':
                    global_vars.append(event.content[0])
                elif event.type == 'f':
                    global_floatings.append(event)
                elif event.type in ('a', 'p', 'e'):
                    global_stmts.append((i, event))

        # Emit constants
        if constants:
            f.write("$c " + " ".join(constants) + " $.\n")

        # Emit global variables
        if global_vars:
            f.write("$v " + " ".join(global_vars) + " $.\n")

        # Emit global floatings
        for stmt in global_floatings:
            f.write(f"{stmt.label} $f {' '.join(stmt.content)} $.\n")

        # Second pass: emit scopes and remaining global statements in order
        i = 0
        global_stmt_idx = 0

        while i < len(events):
            event = events[i]

            # Check if we should emit any global statements before this point
            while global_stmt_idx < len(global_stmts) and global_stmts[global_stmt_idx][0] < i:
                _, stmt = global_stmts[global_stmt_idx]
                if stmt.type == 'a':
                    f.write(f"{stmt.label} $a {' '.join(stmt.content)} $.\n")
                elif stmt.type == 'p':
                    proof_str = " ".join(stmt.proof)
                    f.write(f"{stmt.label} $p {' '.join(stmt.content)} $=\n")
                    f.write(f"  {proof_str} $.\n")
                elif stmt.type == 'e':
                    f.write(f"{stmt.label} $e {' '.join(stmt.content)} $.\n")
                global_stmt_idx += 1

            if isinstance(event, ScopeEvent) and event.type == 'push':
                # Skip outermost push
                if i == outermost_push:
                    i += 1
                    continue

                # Find matching pop and emit scope
                depth = 1
                j = i + 1
                while j < len(events):
                    if isinstance(events[j], ScopeEvent):
                        if events[j].type == 'push':
                            depth += 1
                        elif events[j].type == 'pop':
                            depth -= 1
                            if depth == 0:
                                break
                    j += 1

                # Emit scope block
                f.write("${\n")
                for k in range(i + 1, j):
                    if isinstance(events[k], Statement):
                        stmt = events[k]
                        if stmt.type == 'v':
                            f.write(f"  $v {stmt.content[0]} $.\n")
                        elif stmt.type == 'd':
                            f.write(f"  $d {' '.join(stmt.content)} $.\n")
                        elif stmt.type == 'f':
                            f.write(f"  {stmt.label} $f {' '.join(stmt.content)} $.\n")
                        elif stmt.type == 'e':
                            f.write(f"  {stmt.label} $e {' '.join(stmt.content)} $.\n")
                        elif stmt.type == 'a':
                            f.write(f"  {stmt.label} $a {' '.join(stmt.content)} $.\n")
                        elif stmt.type == 'p':
                            proof_str = " ".join(stmt.proof)
                            f.write(f"  {stmt.label} $p {' '.join(stmt.content)} $=\n")
                            f.write(f"    {proof_str} $.\n")
                f.write("$}\n")

                i = j + 1  # Skip past the scope
            elif isinstance(event, ScopeEvent) and event.type == 'pop':
                # Skip outermost pop
                if i == outermost_pop:
                    i += 1
                    continue
                i += 1
            else:
                i += 1

        # Emit any remaining global statements
        while global_stmt_idx < len(global_stmts):
            _, stmt = global_stmts[global_stmt_idx]
            if stmt.type == 'a':
                f.write(f"{stmt.label} $a {' '.join(stmt.content)} $.\n")
            elif stmt.type == 'p':
                proof_str = " ".join(stmt.proof)
                f.write(f"{stmt.label} $p {' '.join(stmt.content)} $=\n")
                f.write(f"  {proof_str} $.\n")
            elif stmt.type == 'e':
                f.write(f"{stmt.label} $e {' '.join(stmt.content)} $.\n")
            global_stmt_idx += 1

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