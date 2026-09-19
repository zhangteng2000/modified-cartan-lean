import fs from 'node:fs/promises';
import path from 'node:path';

// Enumerate the compiler-recorded import closure. This includes tactic imports;
// recursive logical trust is audited separately with #print axioms.
export async function writeDependencyAudit({ repoDir, buildDir, toolchainLib }) {
  const packages = JSON.parse(await fs.readFile(path.join(buildDir, 'local-packages.json'), 'utf8')).packages;
  const pinned = JSON.parse(await fs.readFile(path.join(repoDir, 'lake-manifest.json'), 'utf8')).packages;
  const roots = [
    { owner: 'local', dir: path.join(buildDir, '.lake/build/lib/lean') },
    ...packages.map(p => ({ owner: p.name, dir: path.join(p.dir, '.lake/build/lib/lean') })),
    { owner: 'lean', dir: toolchainLib }
  ];
  const index = new Map();
  for (const root of roots) {
    let files;
    try { files = await fs.readdir(root.dir, { recursive: true }); }
    catch (error) { if (error.code === 'ENOENT') continue; throw error; }
    for (const file of files) if (file.endsWith('.ilean')) {
      const name = file.slice(0, -6).replaceAll('\\', '.').replaceAll('/', '.');
      if (!index.has(name)) index.set(name, { owner: root.owner, file: path.join(root.dir, file) });
    }
  }
  const graph = new Map();
  const localReferences = [];
  const queued = new Set(['ModifiedCartan']);
  const queue = ['ModifiedCartan'];
  while (queue.length) {
    const batch = queue.splice(0, 16);
    const results = await Promise.allSettled(batch.map(async name => {
      const entry = index.get(name);
      if (!entry) throw new Error('Missing compiler metadata for ' + name);
      const data = JSON.parse(await fs.readFile(entry.file, 'utf8'));
      const imports = data.directImports.map(x => x[0]);
      const references = [];
      if (entry.owner === 'local') for (const key of Object.keys(data.references ?? {})) {
        const ref = JSON.parse(key).c;
        if (ref && typeof ref.m === 'string' && ref.m.startsWith('Mathlib.')) references.push({ module: ref.m, declaration: ref.n });
      }
      return { name, owner: entry.owner, imports, references };
    }));
    for (const result of results) {
      if (result.status === 'rejected') throw result.reason;
      const { name, owner, imports, references } = result.value;
      graph.set(name, { module: name, package: owner, direct_imports: imports });
      if (owner === 'local') localReferences.push({ module: name, mathlib_references: references });
      for (const dep of imports) if (!queued.has(dep)) { queued.add(dep); queue.push(dep); }
    }
  }
  const modules = [...graph.values()].sort((a, b) => a.module.localeCompare(b.module));
  const byPackage = {};
  for (const m of modules) (byPackage[m.package] ??= []).push(m.module);
  const directExternal = [...new Set(modules.filter(m => m.package === 'local').flatMap(m => m.direct_imports).filter(m => graph.get(m).package !== 'local'))].sort();
  const document = {
    schema_version: 1,
    provenance: 'Compiler .ilean directImports from the successful build; includes transitive library and tactic imports, not just constants used in final proof terms.',
    logical_trust_audit: 'axiom-summary.json',
    lean_toolchain: (await fs.readFile(path.join(repoDir, 'lean-toolchain'), 'utf8')).trim(),
    packages: pinned.map(p => ({ name: p.name, revision: p.rev, url: p.url })),
    counts: Object.fromEntries(Object.entries(byPackage).map(([k, v]) => [k, v.length])),
    direct_external_imports: directExternal,
    modules_by_package: byPackage,
    module_graph: modules,
    local_mathlib_references: localReferences.sort((a, b) => a.module.localeCompare(b.module))
  };
  await fs.writeFile(path.join(repoDir, 'verification/dependencies.json'), JSON.stringify(document, null, 2) + '\n');
  return { modules: modules.length, counts: document.counts, direct_external_imports: directExternal.length };
}
