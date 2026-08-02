import sys
sys.stdout.reconfigure(encoding='utf-8')

with open('rh_certificate.lean', 'r', encoding='utf-8') as f:
    content = f.read()

print('First 100 chars:', repr(content[:100]))

fixes = {
    '\u00c3\u00a2\u00e2\u0080\u009e\u00c2\u009a': '\u2102',  # garbled C -> C
    '\u00c3\u00a2\u00e2\u0080\u009e\u00c2\u0099': '\u211d',  # garbled R -> R
    '\u00c3\u0083\u00e2\u0080\u0094': '\u00d7',              # garbled x -> x
}

for bad, good in fixes.items():
    count = content.count(bad)
    if count > 0:
        content = content.replace(bad, good)
        print(f'Fixed {count} instances: {repr(bad)} -> {repr(good)}')

with open('rh_certificate.lean', 'w', encoding='utf-8', newline='\n') as f:
    f.write(content)

print('Done')
