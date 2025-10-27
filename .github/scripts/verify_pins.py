import re,os,sys,urllib.request,json
pat_inline=re.compile(r'^\s*(?:-\s*)?uses:\s*(["\']?)([\w_.-]+\/[\w_.-]+)@([^"\'\s#]+)\1\s*$')
pat_key=re.compile(r'^\s*(?:-\s*)?uses:\s*$')
pat_val=re.compile(r'^\s*(["\']?)([\w_.-]+\/[\w_.-]+)@([^"\'\s#]+)\1\s*$')
files=[]
for d,_,fs in os.walk('.github'):
  for f in fs:
    if f.endswith(('.yml','.yaml')): files.append(os.path.join(d,f))
files.sort()
issues=[]
for f in files:
  L=open(f,'r',encoding='utf-8',errors='ignore').read().splitlines()
  i=0
  while i<len(L):
    ln=L[i]
    m=pat_inline.match(ln)
    if m:
      q,a,r=m.groups()
      if a.startswith('./') or a.startswith('docker://'):
        i+=1; continue
      if not re.fullmatch(r'[0-9a-fA-F]{40}', r):
        issues.append((f,a,r,'NO-SHA'))
      i+=1; continue
    if pat_key.match(ln) and i+1<len(L):
      v=L[i+1]; m2=pat_val.match(v)
      if m2:
        q,a,r=m2.groups()
        if not (a.startswith('./') or a.startswith('docker://')) and not re.fullmatch(r'[0-9a-fA-F]{40}', r):
          issues.append((f,a,r,'NO-SHA'))
        i+=2; continue
    i+=1
if issues:
  for it in issues:
    print('\t'.join(it))
  sys.exit(1)
print('OK')
