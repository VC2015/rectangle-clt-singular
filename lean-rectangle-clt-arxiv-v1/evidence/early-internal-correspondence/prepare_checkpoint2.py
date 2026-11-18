from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
M=json.loads((P/'module-groups.json').read_text());extra=['RectangleCLTCompanion.TiltContractionCovariance','RectangleCLTCompanion.SignedSurfaceScoreExpansion','RectangleCLTCompanion.SplitV4.SymmetricFamilyCount','RectangleCLTCompanion.SplitV4.SymmetricFamilyCountBounds','RectangleCLTCompanion.SplitV4.SymmetricFamilyUnmasked'];targets=json.loads((P/'public-targets.json').read_text());M['groups']['extra']=extra
for m in extra:
 f=R/'../lean-rectangle-clt-singular'/(m.replace('.','/')+'.lean');s=f.read_text();ns=re.search(r'^namespace ([\w.]+)',s,re.M).group(1)
 targets += [ns+'.'+n for n in re.findall(r'^(?:theorem|lemma|def|noncomputable def)\s+([\w.]+)',s,re.M)]
(P/'public-targets2.json').write_text(json.dumps(list(dict.fromkeys(targets)),indent=2)+'\n');(P/'module-groups2.json').write_text(json.dumps(M,indent=2)+'\n')
s=(P/'run_checkpoint.py').read_text().replace("O=P/'checkpoint-1'","O=P/'checkpoint-2'").replace("P/'module-groups.json'","P/'module-groups2.json'").replace("P/'public-targets.json'","P/'public-targets2.json'")
s=s.replace("targets+=private","")
s=s.replace("s=s.replace('Fresh early passage",'''s=s.replace('  let mut queue := targets.toList', '  let privateNames : Array String := #['+', '.join(json.dumps(n) for n in private)+']\\n  let privateTargets := (← getEnv).constants.toList.filterMap fun (n, _) => if privateNames.contains n.toString then some n else none\\n  unless privateTargets.length == privateNames.size do throwError "Missing private target"\\n  let targets := targets ++ privateTargets.toArray\\n  let mut queue := targets.toList');s=s.replace('Fresh early passage''')
s=s.replace("P/'run_checkpoint.py'","P/'run_checkpoint2.py'")
s=s.replace("for m in force:run(","for m in M['groups']['extra']:run(")
s=s.replace("save();run('build',['lake','build']+mods)","r['prior_successful_build_force_receipt']={'path':'evidence/early-internal-correspondence/checkpoint-1/run.json','sha256':sha(P/'checkpoint-1/run.json'),'qualification':'All selected build and force commands passed; only private-name numeric quotation in the type harness failed. Proof source unchanged; exact successful logs are retained.'}; save();run('build-extension',['lake','build']+M['groups']['extra'])")
s=s.replace("'strict_targets':targets","'strict_targets':targets+private")
(P/'run_checkpoint2.py').write_text(s)
