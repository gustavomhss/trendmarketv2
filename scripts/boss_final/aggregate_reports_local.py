import os, json, sys
ARTS=os.environ.get('ARTS_DIR') or os.path.join(os.environ.get('RUNNER_TEMP','.'),'boss-arts')
OUT=os.environ.get('REPORT_DIR') or os.path.join(os.environ.get('RUNNER_TEMP','.'),'boss-aggregate')
os.makedirs(OUT,exist_ok=True)
found=[]
for d,_,fs in os.walk(ARTS):
  for f in fs:
    if f=='report.json':
      try:
        j=json.load(open(os.path.join(d,f),encoding='utf-8'))
        if isinstance(j,dict) and isinstance(j.get('stages'),list):
          found.extend(j['stages'])
      except Exception as e:
        found.append({'name':'unknown','status':'error','errors':[str(e)]})
# sintetiza ausentes s1..s6
names={s.get('name') for s in found}
for i in range(1,7):
  n=f's{i}'
  if n not in names:
    found.append({'name':n,'status':'missing','errors':['artifact not found']})
agg={'stages':found}
json.dump(agg,open(os.path.join(OUT,'report.json'),'w',encoding='utf-8'),ensure_ascii=False)
# imprime status resumido para uso no step seguinte
status={s['name']:s.get('status','missing').upper() for s in found}
print(json.dumps({'status':'FAIL' if any(v!='PASSED' for v in status.values()) else 'PASS','stages':status}))
