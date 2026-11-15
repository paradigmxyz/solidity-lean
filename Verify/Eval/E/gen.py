#!/usr/bin/env python3
"""Lane E fixture generator (docs/eval/e.md).

Emits Lean files over the toy machine of Verify/Eval/E/Toy.lean. Every variant of one family
and size proves the SAME main theorem; only the shape of its proof differs.

  python3 Verify/Eval/E/gen.py <outdir>      # writes every fixture
Families:
  join  : a dispatcher of P=4 paths (DUP1 PUSH1 i EQ PUSH1 A_i JUMPI), each running its own
          block A_i and jumping to one shared block B that ends in STOP.
          variants inline        every path re-steps B, re-proves B's jump destination inline
                   helper        as inline, but the destination fact is one theorem (exp. 1)
                   shared        B is one lemma, general in its stack and gas (exp. 2)
                   perblock      every A_i and B is a lemma; the main theorem only dispatches
  chain : one straight-line block of N opcodes then STOP, cut into k=N/8 blocks of 8 (exp. 3)
          variants mono          one proof stepping all N opcodes (what evm_step emits today)
                   linLit        k block lemmas on literal frames, a right-nested Spec.seq chain
                   balLit        k block lemmas on literal frames, a balanced Triple.seq tree
                   linDef        as linLit with each frame behind a def F_i
                   balDef        as balLit with each frame behind a def F_i
"""
import os, sys

OPS = {'PUSH1': 0x60, 'ADD': 0x01, 'MUL': 0x02, 'POP': 0x50, 'DUP1': 0x80, 'SWAP1': 0x90,
       'JUMPDEST': 0x5b, 'JUMP': 0x56, 'JUMPI': 0x57, 'EQ': 0x14, 'STOP': 0x00}
COST = {'PUSH1': 3, 'ADD': 3, 'MUL': 5, 'POP': 2, 'DUP1': 3, 'SWAP1': 3, 'JUMPDEST': 1,
        'JUMP': 8, 'JUMPI': 10, 'EQ': 3}
GAS0 = 1000000

def body(n, salt=7):
    """n opcodes (a multiple of 3) of the pattern PUSH1 k, ADD, SWAP1 on a stack [a, b, ...]."""
    out = []
    for i in range(n // 3):
        out += [('PUSH1', (salt + i) % 200 + 1), ('ADD',), ('SWAP1',)]
    return out

def assemble(prog):
    """prog: list of ops or ('LABEL', name). PUSH1 of a label is resolved."""
    labels, pc = {}, 0
    for op in prog:
        if op[0] == 'LABEL': labels[op[1]] = pc; continue
        pc += 2 if op[0] == 'PUSH1' else 1
    bs = []
    for op in prog:
        if op[0] == 'LABEL': continue
        bs.append(OPS[op[0]])
        if op[0] == 'PUSH1':
            v = op[1]; bs.append(labels[v] if isinstance(v, str) else v)
    return bs, labels

def nat(bs): return '0x' + ''.join('%02x' % b for b in bs)

class Frame:
    def __init__(self, pc, stk, gvar, off):
        self.pc, self.stk, self.gvar, self.off = pc, list(stk), gvar, off
    def gas(self, off=None):
        o = self.off if off is None else off
        return self.gvar if o == 0 else '%s - %d' % (self.gvar, o)
    def lean(self):
        return '(At %d [%s] (%s))' % (self.pc, ', '.join(self.stk), self.gas())

def word_add(a, b): return '(%s + %s) %% W' % (a, b)

def step(fr, op, bs, labels, valid_proof, seq='Spec.seq', eqval=None):
    """One step from frame fr: (proof-term text of the rule, next frame)."""
    name = op[0]; c = COST.get(name, 0); off2 = fr.off + c
    gas2 = fr.gas(off2)
    hg = '(by omega)'; he = '(by omega)'
    s = fr.stk
    if name == 'PUSH1':
        w = bs[fr.pc + 1]
        t = 'r_push1 (pc\' := %d) (w := %d) (gas\' := %s) rfl rfl rfl %s %s' % (fr.pc + 2, w, gas2, hg, he)
        return t, Frame(fr.pc + 2, [str(w)] + s, fr.gvar, off2)
    if name == 'ADD':
        t = 'r_add (pc\' := %d) (gas\' := %s) rfl rfl %s %s' % (fr.pc + 1, gas2, hg, he)
        return t, Frame(fr.pc + 1, [word_add(s[0], s[1])] + s[2:], fr.gvar, off2)
    if name == 'SWAP1':
        t = 'r_swap1 (pc\' := %d) (gas\' := %s) rfl rfl %s %s' % (fr.pc + 1, gas2, hg, he)
        return t, Frame(fr.pc + 1, [s[1], s[0]] + s[2:], fr.gvar, off2)
    if name == 'DUP1':
        t = 'r_dup1 (pc\' := %d) (gas\' := %s) rfl rfl %s %s' % (fr.pc + 1, gas2, hg, he)
        return t, Frame(fr.pc + 1, [s[0]] + s, fr.gvar, off2)
    if name == 'JUMPDEST':
        t = 'r_jumpdest (pc\' := %d) (gas\' := %s) rfl rfl %s %s' % (fr.pc + 1, gas2, hg, he)
        return t, Frame(fr.pc + 1, s, fr.gvar, off2)
    if name == 'EQ':
        t = 'r_eq (pc\' := %d) (w := %d) (gas\' := %s) rfl rfl (by decide) %s %s' % (fr.pc + 1, eqval, gas2, hg, he)
        return t, Frame(fr.pc + 1, [str(eqval)] + s[2:], fr.gvar, off2)
    if name == 'JUMP':
        d = int(s[0])
        t = 'r_jump (gas\' := %s) rfl %s %s %s' % (gas2, hg, he, valid_proof(d))
        return t, Frame(d, s[1:], fr.gvar, off2)
    if name == 'JUMPI':
        d, k = int(s[0]), int(s[1])
        if k != 0:
            t = 'r_jumpiTaken (gas\' := %s) rfl %s %s (by decide) %s' % (gas2, hg, he, valid_proof(d))
            return t, Frame(d, s[2:], fr.gvar, off2)
        t = 'r_jumpiSkip (pc\' := %d) (gas\' := %s) rfl rfl %s %s rfl' % (fr.pc + 1, gas2, hg, he)
        return t, Frame(fr.pc + 1, s[2:], fr.gvar, off2)
    raise ValueError(name)

def header(ns, bs, extra=''):
    return ('import Verify.Eval.E.Stats\n\n-- Generated by Verify/Eval/E/gen.py. Do not edit.\n\nset_option maxRecDepth 100000\n\n'
            'namespace %s\nopen Verify.Eval.E.Toy\n\n'
            'def code : Nat := %s\ndef size : Nat := %d\n\n%s') % (ns, nat(bs), len(bs), extra)

def footer(ns, main='main'):
    return ('\n#e_stats %s\n#kernel_recheck %s.%s\n\nend %s\n'
            % (ns, ns, main, ns))

def ops_of(prog): return [op for op in prog if op[0] != 'LABEL']

# ---------------------------------------------------------------------------------------
# join
P = 4

def join_prog(N):
    LB = max(3, 3 * round(N / 2 / 3)); LA = max(3, 3 * round(N / 2 / P / 3))
    prog = []
    for i in range(P - 1):
        prog += [('DUP1',), ('PUSH1', i), ('EQ',), ('PUSH1', 'A%d' % i), ('JUMPI',)]
    for i in range(P - 1, -1, -1) if False else range(P):
        pass
    # fallthrough goes to the last path's block
    order = [P - 1] + list(range(P - 1))
    for i in order:
        prog += [('LABEL', 'A%d' % i), ('JUMPDEST',)] + body(LA, 11 * i + 3) + [('PUSH1', 'B'), ('JUMP',)]
    prog += [('LABEL', 'B'), ('JUMPDEST',)] + body(LB, 5) + [('STOP',)]
    return prog

def run_block(fr, ops, bs, labels, valid_proof, eqvals=None, indent='  '):
    """Lines stepping ops from fr in a Spec/Triple goal; returns (lines, frame)."""
    lines = []
    for op in ops:
        if op[0] == 'STOP':
            lines.append(indent + 'exact r_stop rfl'); return lines, None
        ev = None
        if op[0] == 'EQ': ev = eqvals.pop(0)
        t, fr = step(fr, op, bs, labels, valid_proof, eqval=ev)
        lines.append(indent + 'refine Triple.seq (%s) ?_' % t)
    return lines, fr

def path_ops(prog, labels, j):
    """The opcodes path x=j runs: dispatcher prefix, A_j, B; and the EQ results."""
    ops = ops_of(prog)
    seq, eqv, i = [], [], 0
    # dispatcher
    for t in range(P - 1):
        seq += ops[5 * t:5 * t + 5]; eqv.append(1 if t == j else 0)
        if t == j: break
    return seq, eqv

def block_ops(prog, label):
    out, on = [], False
    for op in prog:
        if op[0] == 'LABEL':
            if on: break
            on = op[1] == label; continue
        if on: out.append(op)
        if on and op[0] in ('JUMP', 'STOP'): break
    return out

def cost(ops): return sum(COST.get(o[0], 0) for o in ops)

def gen_join(N, variant, outdir):
    prog = join_prog(N); bs, labels = assemble(prog)
    ns = 'Verify.Eval.E.Fx.Join%d_%s' % (N, variant)
    pcB = labels['B']
    shared_valid = variant != 'inline'
    def vp(d):
        if d == pcB and shared_valid: return 'vB'
        return '(rfl : valid code size %d = true)' % d
    extra = ''
    if shared_valid:
        extra += 'theorem vB : valid code size %d = true := rfl\n\n' % pcB
    Bops = block_ops(prog, 'B')
    costB = cost(Bops)
    if variant in ('shared', 'perblock'):
        fr = Frame(pcB, ['a', 'b'], 'g', 0)
        lines, _ = run_block(fr, Bops, bs, labels, vp)
        extra += ('theorem blockB (a b g : Nat) (hG : %d ≤ g) :\n    Spec code size (At %d [a, b] g) (fun _ => True) := by\n'
                  % (costB, pcB)) + '\n'.join(lines) + '\n\n'
    if variant == 'perblock':
        for i in range(P):
            Aops = block_ops(prog, 'A%d' % i)
            fr = Frame(labels['A%d' % i], ['a', 'b'], 'g', 0)
            lines, fr2 = run_block(fr, Aops, bs, labels, vp)
            # last line is the JUMP into B: close with the B lemma
            lines.append('  exact blockB _ _ _ (by omega)')
            extra += ('theorem blockA%d (a b g : Nat) (hG : %d ≤ g) :\n    Spec code size (At %d [a, b] g) (fun _ => True) := by\n'
                      % (i, cost(Aops) + costB, labels['A%d' % i])) + '\n'.join(lines) + '\n\n'
    alts = ' ∨ '.join('x = %d' % j for j in range(P))
    out = [header(ns, bs, extra)]
    out.append('theorem main (x y g : Nat) (hx : x < %d) (hG : %d ≤ g) :\n    Spec code size (At 0 [x, y] g) (fun _ => True) := by' % (P, GAS0))
    out.append('  rcases (by omega : %s) with %s <;> subst h' % (alts, ' | '.join(['h'] * P)))
    for j in range(P):
        seqops, eqv = path_ops(prog, labels, j)
        fr = Frame(0, [str(j), 'y'], 'g', 0)
        # concrete stack entries for the dispatcher: DUP1 PUSH1 i EQ PUSH1 A JUMPI
        lines, fr = run_block(fr, seqops, bs, labels, vp, eqvals=list(eqv), indent='    ')
        # where did it land?
        lab = 'A%d' % j
        assert fr.pc == labels[lab], (fr.pc, labels[lab], j)
        Aops = block_ops(prog, lab)
        if variant == 'perblock':
            lines.append('    exact blockA%d _ _ _ (by omega)' % j)
        else:
            l2, fr = run_block(fr, Aops, bs, labels, vp, indent='    ')
            lines += l2
            if variant == 'shared':
                lines.append('    exact blockB _ _ _ (by omega)')
            else:
                l3, _ = run_block(fr, Bops, bs, labels, vp, indent='    ')
                lines += l3
        lines[0] = '  · ' + lines[0].lstrip()
        out.append('\n'.join(lines))
    src = '\n'.join(out) + '\n' + footer(ns)
    nunique = len(ops_of(prog))
    write(outdir, 'Join%d_%s' % (N, variant), src)
    return nunique

# ---------------------------------------------------------------------------------------
# chain
BLK = 8

def chain_prog(N):
    n = 3 * (N // 3) if N % 3 else N
    ops = body(n, 9)
    while len(ops) < N: ops.append(('JUMPDEST',))
    return ops + [('STOP',)]

def frames_of(ops, bs):
    fr = Frame(0, ['x', 'y'], 'g', 0); frs = [fr]; terms = []
    for op in ops[:-1]:
        t, fr = step(fr, op, bs, {}, None); frs.append(fr); terms.append(t)
    return frs, terms

def tree(items):
    if len(items) == 1: return items[0]
    m = len(items) // 2
    return 'Triple.seq (%s) (%s)' % (tree(items[:m]), tree(items[m:]))

def gen_chain(N, variant, outdir):
    ops = chain_prog(N); bs, _ = assemble(ops)
    ns = 'Verify.Eval.E.Fx.Chain%d_%s' % (N, variant)
    frs, terms = frames_of(ops, bs)
    k = N // BLK
    stmt = 'theorem main (x y g : Nat) (hG : %d ≤ g) :\n    Spec code size (At 0 [x, y] g) (fun _ => True) := by\n' % GAS0
    extra = ''
    if variant == 'mono':
        body_ = '\n'.join('  refine Triple.seq (%s) ?_' % t for t in terms) + '\n  exact r_stop rfl'
        src = header(ns, bs) + stmt + body_ + '\n' + footer(ns)
    else:
        lit = variant.endswith('Lit')
        def F(i):
            return frs[i * BLK].lean() if lit else '(F%d x y g)' % i
        if not lit:
            for i in range(k + 1):
                extra += 'def F%d (x y g : Nat) : St → Prop := %s\n' % (i, frs[i * BLK].lean())
            extra += '\n'
        for i in range(k):
            ts = terms[i * BLK:(i + 1) * BLK]
            pre = '' if lit else '  unfold F%d F%d\n' % (i, i + 1)
            extra += ('theorem blk%d (x y g : Nat) (hG : %d ≤ g) :\n    Triple (Step code size) %s %s := by\n%s'
                      % (i, GAS0, F(i), F(i + 1), pre))
            extra += '\n'.join('  refine Triple.seq (%s) ?_' % t for t in ts) + '\n  exact Triple.refl\n\n'
        last = '(r_stop rfl)' if lit else '(by unfold F%d; exact r_stop rfl)' % k
        bl = ['(blk%d x y g hG)' % i for i in range(k)]
        if variant.startswith('lin'):
            term = last
            for b in reversed(bl): term = 'Spec.seq %s (%s)' % (b, term)
        else:
            term = 'Spec.seq (%s) %s' % (tree(bl), last)
        pre = '' if lit else '  show Spec code size (F0 x y g) _\n'
        src = header(ns, bs, extra) + stmt + pre + '  exact ' + term + '\n' + footer(ns)
    write(outdir, 'Chain%d_%s' % (N, variant), src)
    return N

# ---------------------------------------------------------------------------------------
# solm: Verify/Basic.lean's SolM (Loom wp). One sub-program S of L storage updates appears in
# both branches of prog c := if c then (sstore 0 1; S) else (sstore 0 2; S).
#   inline : simp the weakest precondition of the whole program; S's VC is computed twice
#   shared : S's frame fact (slot 0 kept) is one lemma, each branch uses it by wp_cons

def gen_solm(L, variant, outdir):
    ns = 'Verify.Eval.E.Fx.SolM%d_%s' % (L, variant)
    lines = ['import Verify.Basic', 'import Verify.Eval.E.Stats', '',
             '-- Generated by Verify/Eval/E/gen.py. Do not edit.', '',
             'set_option maxRecDepth 100000', '',
             'namespace %s' % ns, 'open SolidCore.Verify', '',
             '/-- The shared sub-program: L storage updates of slots 1..L. -/',
             'def S : SolM Unit := do']
    for i in range(L):
        lines.append('  sstore %d ((← sload %d) + %d)' % (i + 1, i + 1, i + 1))
    lines += ['', 'def prog (c : Bool) : SolM Unit :=',
              '  if c then (do sstore 0 1; S) else (do sstore 0 2; S)', '']
    if variant == 'shared':
        lines += ['theorem S_keeps (herr : Revert → Prop) (s : Storage) :',
                  '    wp S (fun _ _ s\' => s\' 0 = s 0) herr s := by',
                  '  simp (config := { maxSteps := 100000000 }) only [S, wp_bind, wp_sload, wp_sstore]',
                  '  simp (config := { maxSteps := 100000000 })', '']
        lines += ['theorem main (c : Bool) (herr : Revert → Prop) (s : Storage) :',
                  '    wp (prog c) (fun _ _ s\' => 0 < s\' 0) herr s := by',
                  '  cases c <;> simp (config := { maxSteps := 100000000 }) only [prog, wp_bind, wp_sstore, Bool.false_eq_true, ite_false, ite_true]',
                  '  all_goals',
                  '    refine wp_cons S _ _ ?_ herr _ (S_keeps herr _)',
                  '    intro _ _ s\' h; simp only at h ⊢; rw [h]; simp', '']
    else:
        lines += ['theorem main (c : Bool) (herr : Revert → Prop) (s : Storage) :',
                  '    wp (prog c) (fun _ _ s\' => 0 < s\' 0) herr s := by',
                  '  cases c <;> simp (config := { maxSteps := 100000000 }) only [prog, S, wp_bind, wp_sload, wp_sstore, Bool.false_eq_true, ite_false, ite_true]',
                  '  all_goals simp (config := { maxSteps := 100000000 })', '']
    src = '\n'.join(lines) + footer(ns)
    write(outdir, 'SolM%d_%s' % (L, variant), src)

def write(outdir, name, src):
    with open(os.path.join(outdir, name + '.lean'), 'w') as f: f.write(src)

if __name__ == '__main__':
    outdir = sys.argv[1]; os.makedirs(outdir, exist_ok=True)
    sizes = [16, 32, 64, 128, 256]
    for N in sizes:
        for v in ['inline', 'helper', 'shared', 'perblock']:
            u = gen_join(N, v, outdir)
        print('join', N, 'unique opcodes', u)
        for v in ['mono', 'linLit', 'balLit', 'linDef', 'balDef']:
            gen_chain(N, v, outdir)
        for v in ['inline', 'shared']:
            gen_solm(N, v, outdir)
