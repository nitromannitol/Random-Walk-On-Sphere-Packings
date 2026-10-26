import os,sys,json,hashlib,re,subprocess,pathlib,time
P=pathlib.Path.cwd();O=P/'diagnostic-output';O.mkdir(exist_ok=True)
LOCK=str(pathlib.Path(os.environ['RUNNER_TEMP'])/'lean-build.lock');CAP='12884901888'
def run(args,*,env=None,cwd=None,output=None):
    command=[str(x) for x in args]
    with (O/'commands.jsonl').open('a') as f:f.write(json.dumps({'argv':command,'cwd':str(cwd or P),'at':time.time()})+'\n')
    if output:
        with (O/output).open('w') as f:
            p=subprocess.run(command,cwd=cwd or P,env=env,stdout=f,stderr=subprocess.STDOUT)
    else:p=subprocess.run(command,cwd=cwd or P,env=env)
    if p.returncode:raise RuntimeError(f'command failed ({p.returncode}): {command}; log={output}')
    return p
lean=pathlib.Path(subprocess.check_output(['elan','which','lean'],text=True).strip());lake=lean.parent/'lake'
assert hashlib.sha256(lean.read_bytes()).hexdigest()=='bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38'
def locked(args,**kw):return run(['/usr/bin/flock','-x',LOCK,'/usr/bin/prlimit','--as='+CAP,'--',*args],**kw)
manifest=json.loads((P/'lake-manifest.json').read_text())
packages={x['name'].removeprefix('«').removesuffix('»'):P/'.lake/packages'/x['name'].removeprefix('«').removesuffix('»') for x in manifest['packages']}
for x in manifest['packages']:
    name=x['name'].removeprefix('«').removesuffix('»');d=packages[name];d.mkdir(parents=True,exist_ok=True)
    run(['git','init',d],output='fetch-'+name+'.log')
    run(['git','-C',d,'remote','add','origin',x['url']],output='remote-'+name+'.log')
    run(['git','-C',d,'fetch','--depth=1','origin',x['rev']],output='fetch-'+name+'.log')
    run(['git','-C',d,'checkout','--detach',x['rev']],output='checkout-'+name+'.log')
# Bootstrap only the exact pinned cache client's small source closure, serially.
# No Lake process, configuration edit, toolchain wrapper or project build cache is used.
bootstrap_roots=list(packages.values());core=lean.parent.parent/'lib/lean'
cacheenv=os.environ.copy();cacheenv['LEAN_PATH']=os.pathsep.join([str(d/'.lake/build/lib/lean') for d in bootstrap_roots]+[str(core)])
cacheenv['LEAN_SRC_PATH']=os.pathsep.join(str(d) for d in bootstrap_roots)
cache_seen=set()
def cache_build(module):
    if module in cache_seen:return
    cache_seen.add(module);rel=pathlib.Path(*module.split('.')).with_suffix('.lean')
    match=next(((d,d/rel) for d in bootstrap_roots if (d/rel).is_file()),None)
    if match is None:return
    root,source=match
    for group in re.findall(r'(?m)^(?:(?:public|private|meta) )*import\s+([^\n]+)',source.read_text()):
        for dep in group.split('--')[0].split():cache_build(dep)
    out=root/'.lake/build/lib/lean'/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
    locked([lean,'-j1','-o',out,source],cwd=root,env=cacheenv,output='bootstrap-'+module+'.log')
cache_build('Cache.Main')
mathlib=packages['mathlib']
# Preserve the pinned package layout expected by the official cache client.
for n,d in packages.items():
    if n=='mathlib':continue
    link=mathlib/'.lake/packages'/n;link.parent.mkdir(parents=True,exist_ok=True);link.symlink_to(d,target_is_directory=True)
locked([lean,'-j1','--run',mathlib/'Cache/Main.lean','get'],cwd=mathlib,env=cacheenv,output='cache.log')
bindings=[]
for x in manifest['packages']:
    d=packages[x['name'].removeprefix('«').removesuffix('»')];head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip();assert head==x['rev'],(x['name'],head,x['rev'])
    bindings.append({'name':x['name'].removeprefix('«').removesuffix('»'),'commit':head})
assert next(x for x in bindings if x['name']=='mathlib')['commit']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
(O/'bindings.json').write_text(json.dumps({'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'lean_sha256':hashlib.sha256(lean.read_bytes()).hexdigest(),'dependencies':bindings},indent=2)+'\n')
# No old project artifact is restored. Only exact pinned Mathlib cache data is used.
roots=[P]+[d for n,d in packages.items() if n=='lattice-probability']
builds=[d/'.lake/build/lib/lean' for d in roots]
for d in builds:d.mkdir(parents=True,exist_ok=True)
trusted=[d/'.lake/build/lib/lean' for n,d in packages.items() if n!='lattice-probability']+[lean.parent.parent/'lib/lean']
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(str(d) for d in [*builds,*trusted])
trustedenv=env.copy();trustedenv['LEAN_PATH']=os.pathsep.join(str(d) for d in trusted)
seen=set()
def build(module):
    if module in seen:return
    seen.add(module);rel=pathlib.Path(*module.split('.')).with_suffix('.lean')
    match=next(((d,d/rel) for d in roots if (d/rel).is_file()),None)
    if match is None:return
    root,source=match
    imports=re.findall(r'(?m)^(?:(?:public|private|meta) )*import\s+([^\n]+)',source.read_text())
    for group in imports:
        for dep in group.split('--')[0].split():build(dep)
    out=root/'.lake/build/lib/lean'/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
    opts=['-DautoImplicit=false'] if root!=P else ([] if MODE=='sphere' and module.startswith('BouRabeeGwynne.') else ['-DautoImplicit=false','-DrelaxedAutoImplicit=false'])
    print('COMPILE',module,flush=True)
    locked([lean,'-j1',*opts,'-o',out,source],cwd=root,env=env,output='build-'+module+'.log')
    with (O/'compiled.jsonl').open('a') as f:f.write(json.dumps({'module':module,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'olean_sha256':hashlib.sha256(out.read_bytes()).hexdigest()})+'\n')
MODE='sphere'
# Check the exact original definition in a distinct physical output directory.
build('BouRabeeGwynne.PaperObjects')
base_revision='f4d021bc8a311a64d835230928adef8bf905f113'
base_source=subprocess.check_output(['git','show',base_revision+':BouRabeeGwynne/LipschitzDomain.lean'],text=True)
base_root=O/'baseline-source';base_file=base_root/'BouRabeeGwynne/LipschitzDomain.lean'
base_file.parent.mkdir(parents=True,exist_ok=True);base_file.write_text(base_source)
base_lib=O/'baseline/lib/lean';base_out=base_lib/'BouRabeeGwynne/LipschitzDomain.olean'
base_out.parent.mkdir(parents=True,exist_ok=True)
# Lean selects a namespace directory from the first search-path entry. Mirror
# the already built, unchanged imports into this separate output view.
for artifact in builds[0].rglob('*'):
    if not artifact.is_file():continue
    relative=artifact.relative_to(builds[0])
    if str(relative).startswith('BouRabeeGwynne/LipschitzDomain.'):continue
    target=base_lib/relative;target.parent.mkdir(parents=True,exist_ok=True)
    assert not target.exists() and not target.is_symlink()
    target.symlink_to(artifact)
base_env=env.copy();base_env['LEAN_PATH']=str(base_lib)+os.pathsep+env['LEAN_PATH']
locked([lean,'-j1','-o',base_out,base_file],cwd=base_root,env=base_env,output='baseline-definition.log')

def check_probe(name,text,probe_env):
    source=O/(name.replace('-','_')+'.lean');source.write_text(text)
    locked([lean,'-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DwarningAsError=true',source],env=probe_env,output=name+'.log')

check_probe('original-definition-equality',r"""import BouRabeeGwynne.LipschitzDomain
open BouRabeeGwynne
example : (Nat.cast (R := ℝ≥0∞) 2) = (2 : ℝ≥0∞) := by rfl
example (d : ℕ) (q : Euc (d - 1)) (t : ℝ) :
    (WithLp.toLp (Nat.cast (R := ℝ≥0∞) 2)
      (fun i => Option.casesOn i t (fun j => q j)) :
      EuclideanSpace ℝ (Option (Fin (d - 1)))) =
    cylinderCoordinates (d := d) q t := by rfl
""",base_env)
build('BouRabeeGwynne.LipschitzDomain')
check_probe('revised-definition-equality',r"""import BouRabeeGwynne.LipschitzDomain
open BouRabeeGwynne
example (d : ℕ) (q : Euc (d - 1)) (t : ℝ) :
    cylinderCoordinates (d := d) q t =
      (WithLp.toLp 2 (fun i => Option.casesOn i t (fun j => q j)) :
        EuclideanSpace ℝ (Option (Fin (d - 1)))) := by rfl
example (d : ℕ) (q : Euc (d - 1)) (t : ℝ) :
    (cylinderCoordinates (d := d) q t) none = t := by rfl
example (d : ℕ) (q : Euc (d - 1)) (t : ℝ) (j : Fin (d - 1)) :
    (cylinderCoordinates (d := d) q t) (some j) = q j := by rfl
#print axioms BouRabeeGwynne.cylinderCoordinates
""",env)
# Real geometry consumers exercise reconstruction, norm and exterior-ball APIs.
build('BouRabeeGwynne.LipschitzLocalExteriorBalls')
build('SpherePackingsAudit.Vocabulary.BouRabeeGwynne.LipschitzDomain')
challenge=P/'SpherePackingsAudit/TheoremA/Challenge.lean'
assert hashlib.sha256(challenge.read_bytes()).hexdigest()=='720cf2ff00523bb5b3517c636ef8a9ca7b5e507778652e512ea394507365d5be'
canonical=O/'canonical';alias='PalomarCanonical15d1a49827b361d0ae68e5d4.Challenge';olean=canonical/pathlib.Path(*alias.split('.')).with_suffix('.olean');olean.parent.mkdir(parents=True,exist_ok=True)
locked([lean,'-j1','-o',olean,challenge],env=trustedenv,output='canonical-build.log')
canenv=trustedenv.copy();canenv['LEAN_PATH']=str(canonical)+os.pathsep+trustedenv['LEAN_PATH']
locked([lean.parent/'leanexport',alias,'--','BouRabeeGwynne.cylinderCoordinates'],env=canenv,output='canonical.ndjson')
locked([lean.parent/'leanexport','BouRabeeGwynne.LipschitzDomain','--','BouRabeeGwynne.cylinderCoordinates'],env=env,output='defining-module.ndjson')
locked([lean,'-j1','--run',P/'.github/diagnostics/CompareExports.lean',O/'canonical.ndjson',O/'defining-module.ndjson'],output='comparison.log')
comparison=(O/'comparison.log').read_text()
assert 'COMPARE BouRabeeGwynne.cylinderCoordinates: ConstantInfo=true; type=true' in comparison, 'Root ABI still differs'
assert re.search(r'CLOSURE checked=\d+; mismatches=0(?:\s|$)',comparison), 'Dependency closure still differs'
(O/'scope.txt').write_text('Actual canonical Challenge versus real narrow defining module, with original/revised all-carrier rfl checks, none/some coordinate checks and real geometry-consumer builds. This is not full Solution ABI evidence or an official comparator acceptance. No predicates, types, Frozen statements, definition_names or comparator rules changed.\n')
(O/'summary.json').write_text(json.dumps({'state':'PASS_NARROW_DEFINITIONAL_EQUALITY_AND_ABI','original_and_revised_all_carrier_rfl_checks':True,'coordinate_none_some_checks':True,'geometry_consumers_built':True,'vocabulary_context_built':True,'root_constant_info_equal':True,'root_closure_mismatches':0,'full_solution_comparator':False,'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()},indent=2)+'\n')
