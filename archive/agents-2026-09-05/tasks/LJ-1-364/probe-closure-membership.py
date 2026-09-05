# LJ-1.364 probe: is L/Coding/Model in BOTH trophy closures today?
# Reuses ledger.py's own graph and closure code so the answer shares its caliber.
import sys, tomllib
sys.path.insert(0, "scripts/measure")
import importlib.util

spec = importlib.util.spec_from_file_location("ledger", "scripts/measure/ledger.py")
ledger = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ledger)

with open("dev/ledger.toml", "rb") as f:
    data = tomllib.load(f)

files = ledger.tracked_masters()
cfg = data.get("reuse", {})
ac_root, gch_root = cfg["ac_root"], cfg["gch_root"]
graph = ledger.import_graph(files)
ac = ledger.closure(graph, [ac_root])
gch = ledger.closure(graph, [gch_root])

target = "src/L/Coding/Model.lagda.md"
print(f"ac_root={ac_root}  gch_root={gch_root}")
print(f"target in AC closure:  {target in ac}")
print(f"target in GCH closure: {target in gch}")
shared = sorted(ac & gch)
print(f"shared masters: {len(shared)}")
for m in shared:
    print("  ", m)
