import re
import pyperclip

content = ""
with open('main.typ') as f:
    content = f.read()

splits = content.split('$')
evens = splits[0::2]
odds = splits[1::2]
# print(odds)

truefunc_list = ['clo', 'abs', 'norm', 'card']

truefunc_indices = {f: [] for f in truefunc_list}
for i,odd in enumerate(odds):
    for tf in truefunc_list:
        if tf in odd:
            truefunc_indices[tf].append(i)

delim_pairs = {
    '{': '}',
    '(': ')',
    '[': ']'
}
uscore_pat = re.compile(r'_\(')
upper_pat = re.compile(r'\^\(')

simple_translations = {
    'plus.circle.big': '\\bigoplus',
    'plus.big.circle': '\\bigoplus',
    'subset.eq': '\\subseteq',
    'colon.eq': '\\coloneqq',
    'union.dot': '\\cupdot',
    'infinity': '\\infty',
    'square': '\\square',
    'lip': '\\lip',
    'ihom': '\\ihom',
    'bcn': '\\bcn',
    'bbox': '\\bbox',
    'exists': '\\exists',
    'forall': '\\forall',
    'pi': '\\pi',
    '<=>': '\\Leftrightarrow',
    '<=': '\\leq',
    '>=': '\\geq',
    '->': '\\to',
    'ell': '\\ell',
    'induced': '\\induced',
    'gamma': '\\gamma',
    'sigma': '\\sigma',
    'alpha': '\\alpha',
    'phi': '\\phi',
    ' in ': ' \\in ',
}

def find_matching_delim(l, pos):
    base = l[pos]
    target = delim_pairs[base]
    count = 1
    for i in range(pos+1, len(l)):
        if l[i] == target:
            count -= 1
        elif l[i] == base:
            count += 1
        if count == 0:
            return i
    return None

def fix_attachments(l):
    while (m := uscore_pat.search(l)):
        par_s = m.end(0)-1
        par_e = find_matching_delim(l, par_s)
        l0 = l[:par_s]
        l1 = '{' + l[par_s+1:par_e] + '}'
        l2 = l[par_e+1:]
        l = ''.join((l0,l1,l2))
    while (m := upper_pat.search(l)):
        par_s = m.end(0)-1
        par_e = find_matching_delim(l, par_s)
        l0 = l[:par_s]
        l1 = '{' + l[par_s+1:par_e] + '}'
        l2 = l[par_e+1:]
        l = ''.join((l0,l1,l2))
    return l



# should be done first
def fix_sets(l):
    l = l.replace('{', '\\{')
    return l.replace('}', '\\}')

def apply_simple_translations(l):
    for t in simple_translations:
        l = l.replace(t, simple_translations[t])
    return l

odds = [fix_sets(l) for l in odds]
odds = [fix_attachments(l) for l in odds]

for tf in truefunc_list:
    pat = re.compile(f'{tf}\\(')
    for index in truefunc_indices[tf]:
        line = odds[index]
        while (m := pat.search(line)):
            s = m.start(0)
            par_s = m.end(0)-1
            par_e = find_matching_delim(line, par_s)
            l0 = line[:s]
            l1 = '\\' + line[s:par_s]
            l2 = '{' + line[par_s+1:par_e] + '}'
            l3 = line[par_e+1:]
            line = ''.join((l0,l1,l2,l3))
        odds[index] = line

odds = [apply_simple_translations(l) for l in odds]
buck = [val for pair in zip(evens, odds) for val in pair]
if len(evens) > len(odds):
    buck.append(evens[-1])
fulldoc = '$'.join(buck)

section_names = ['lemma', 'theorem', 'definition', 'proof']

def fix_section(l, sn):
    pat = re.compile(f'#{sn}\\[')
    tagpat = re.compile(r'\s*<(.*?)>')
    while (m := pat.search(l)):
        s = m.start(0)
        par_s = m.end(0)-1
        par_e = find_matching_delim(l, par_s)
        tag = tagpat.match(l, par_e+1)
        tag_e = par_e
        
        pre_sec = l[:s]
        sec_innards = l[par_s+1:par_e]
        label = ""
        if tag:
            tag_innards = tag.group(1)
            label = f'\\label{{{tag_innards}}}'
            tag_e = tag.end(0)
        post_sec = l[tag_e+1:]

        l = pre_sec + f'\\begin{{{sn}}} {label}\n' + sec_innards + f'\\end{{{sn}}}\n' + post_sec
    return l
fulldoc = fulldoc.replace('#annotation', '\\annotation')
for sn in section_names:
    fulldoc = fix_section(fulldoc, sn)
pyperclip.copy(fulldoc)