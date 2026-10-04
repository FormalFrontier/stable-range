#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only controls for the fixed Stable Range native-record adapter.

Synthetic markup from shipped signatures exercises refusals, not the genuine
native-record provenance. Run separate native generation and --check for that.
"""

import copy
from html import escape
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

import generate_api as api


ROOT = Path(__file__).resolve().parent.parent


def fixture():
    entries = re.findall(r"^### ([^\n]+)\n\n```lean\n([^\n]+)\n```\n\n(.*?)\n\n\[Source\]",
                         (ROOT / "docs/API.md").read_text(), re.M | re.S)
    api.require(len(entries) == 121 and len({name for name, _, _ in entries}) == 121,
                "synthetic fixture signatures differ")
    records = {module: dict(name=module, imports=copy.deepcopy(meta["imports"]),
                            instances=copy.deepcopy(meta["instances"]), declarations=[])
               for module, meta in api.EXPECTED_MODULES.items()}
    sources = {path: (ROOT / path).read_bytes() for path in api.INPUTS
               if path != "tests/PublicAPIClient.lean"}
    sources["tests/PublicAPIClient.lean"] = (
        ROOT / "tests/StableRangeTests/PublicAPIClient.lean").read_bytes()
    for name, signature, prose in entries:
        api.require(name in api.EXPECTED, "synthetic fixture has unknown name")
        meta = api.EXPECTED[name]
        prefix = meta["display_kind"] + " " + name
        api.require(signature.startswith(prefix), "synthetic fixture identity differs")
        header = ('<div class="decl_header"><span class="decl_kind">'
                  + escape(meta["display_kind"]) + '</span> '
                  + '<span class="decl_name">' + escape(name) + '</span>'
                  + '<span>' + escape(signature[len(prefix):]) + '</span></div>')
        module = meta["module"]
        path = api.MODULE_PATHS[module]
        doc = "" if name in api.NOTES else prose
        records[module]["declarations"].append(dict(header=header, info=dict(
            name=name, kind=meta["kind"], line=meta["line"],
            sourceLink=api.SOURCE_SNAPSHOT + api.SOURCE + "/" + path,
            docLink="./" + module.replace(".", "/") + ".html#" + name,
            doc=doc)))
    return records, sources


def first(records):
    return records[api.MODULES[0]]["declarations"][0]


class Controls(unittest.TestCase):
    def test_full_inventory_and_all_module_records(self):
        records, sources = fixture()
        markdown, raw_manifest = api.render(records, api.SOURCE, sources)
        manifest = json.loads(raw_manifest)
        self.assertEqual(markdown.count(b"\n### "), 121)
        self.assertEqual(markdown.count(b"**API note (not a source docstring):**"), 23)
        self.assertEqual(manifest["library_display_sites"], 121)
        self.assertEqual(manifest["boundary_client_display_sites"], 0)
        self.assertEqual(set(manifest["inputs"]), set(api.INPUTS))
        self.assertEqual(len(manifest["inputs"]), 18)
        self.assertEqual(set(manifest["documentation_inputs"]),
                         set(api.DOCUMENTATION_INPUTS))
        self.assertEqual(manifest["analyzed_source_revision"], api.SOURCE)
        self.assertEqual(manifest["analyzed_source_tree"], api.SOURCE_TREE)
        self.assertEqual(manifest["native_range_binding"]["range_map_sha256"],
                         api.RANGE_MAP_SHA256)
        self.assertEqual(manifest["native_range_binding"]["native_database_sha256"],
                         api.NATIVE_DATABASE_SHA256)
        self.assertEqual(manifest["docgen_revision"], api.TOOL)
        self.assertEqual(manifest["modules"], list(api.MODULES))
        self.assertEqual(len(manifest["native_record_canonical_sha256"]), 14)
        self.assertIn(b"not a raw/private/generated declaration census", markdown)
        self.assertIn(b"## PublicAPIClient\n\nScope: private regression client", markdown)
        self.assertIn(b"## StableRange\n\nScope: aggregate public-import root", markdown)
        self.assertIn(b"../StableRange/Basic.lean#L30", markdown)
        self.assertNotIn(b"../tests/StableRange.lean", markdown)
        self.assertFalse(manifest["proof_certification"])
        self.assertFalse(manifest["release_acceptance"])
        for module in ("StableRange", "PublicAPIClient"):
            self.assertEqual(records[module]["declarations"], [])
            self.assertIn(module, manifest["native_record_canonical_sha256"])

    def test_literal_headers_and_source_prose(self):
        records, sources = fixture()
        markdown, _ = api.render(records, api.SOURCE, sources)
        for module in api.MODULES:
            for row in records[module]["declarations"]:
                header = api.Header(row["header"]).rendered()
                self.assertIn(header.encode(), markdown)
                self.assertEqual(api.digest(header.encode()),
                                 api.EXPECTED[row["info"]["name"]]["header_sha256"])
        self.assertIn(b"[Nontrivial R]", markdown)
        self.assertIn(b"[Nonempty o]", markdown)
        self.assertIn(b"noncomputable def Matrix.rowRank", markdown)
        self.assertIn(b"{s n :", markdown)

    def test_header_parser_entities_and_invalid_markup(self):
        self.assertEqual(api.Header('<div><span>{A : Type u}</span> :'
                                    '<div class="decl_type">x &lt; y ∧ x ≤ y</div></div>').rendered(),
                         '{A : Type u} : x < y ∧ x ≤ y')
        for text in ('<script>x</script>', '<div><span></div>', '<div>unclosed',
                     '<span onclick="x">x</span>', '<div><!--comment--></div>',
                     '<!DOCTYPE html>', 'outside', '<div/>tail'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                api.Header(text)

    def test_module_name_kind_and_omission_refusals(self):
        mutations = [
            lambda records: records.pop(api.MODULES[-1]),
            lambda records: records.update(Other=dict(name="Other", imports=[],
                                                      instances=[], declarations=[])),
            lambda records: records[api.MODULES[0]]["declarations"].pop(),
            lambda records: records[api.MODULES[0]]["declarations"].append(
                copy.deepcopy(first(records))),
            lambda records: records[api.MODULES[1]]["declarations"].append(
                copy.deepcopy(first(records))),
            lambda records: records["StableRange"]["declarations"].append(
                copy.deepcopy(first(records))),
            lambda records: records["PublicAPIClient"].update(name="ClientChanged"),
            lambda records: records[api.MODULES[0]]["imports"].append("Invented"),
            lambda records: records[api.MODULES[0]]["instances"].append("Invented"),
        ]
        for key, value in (("name", "Wrong"), ("kind", "axiom"), ("line", 0),
                           ("line", 999999), ("line", True), ("docLink", "wrong"),
                           ("doc", "```inject")):
            mutations.append(lambda records, field=key, changed=value:
                             first(records)["info"].update({field: changed}))
        for index, mutate in enumerate(mutations):
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                records, sources = fixture()
                mutate(records)
                api.render(records, api.SOURCE, sources)

    def test_signature_and_docstring_drift(self):
        for needle in ("theorem", "noncomputable", "[Nonempty n]", "[Ring R]"):
            records, sources = fixture()
            row = next(row for record in records.values() for row in record["declarations"]
                       if needle in api.Header(row["header"]).rendered())
            row["header"] = row["header"].replace(needle, "changed", 1)
            with self.subTest(needle=needle), self.assertRaises(ValueError):
                api.render(records, api.SOURCE, sources)
        for has_doc in (True, False):
            records, sources = fixture()
            row = next(row for record in records.values() for row in record["declarations"]
                       if bool(row["info"]["doc"]) == has_doc)
            row["info"]["doc"] += " fabricated text"
            with self.subTest(has_doc=has_doc), self.assertRaises(ValueError):
                api.render(records, api.SOURCE, sources)

    def test_source_snapshot_path_line_and_revision(self):
        records, sources = fixture()
        valid = first(records)["info"]["sourceLink"]
        changes = [valid.replace("source-snapshot/", "source/"),
                   "https://github.com/FormalFrontier/stable-range/blob/" +
                   valid.removeprefix("source-snapshot/"),
                   valid.replace(api.SOURCE, "b" * 40),
                   valid.replace("Basic.lean", "Wrong.lean"),
                   valid + "?query=1", valid + "\n", valid + "#L1-L2",
                   valid.replace("/StableRange/Basic.lean", "/tests/Basic.lean")]
        for value in changes:
            with self.subTest(source_link=value), self.assertRaises(ValueError):
                altered = copy.deepcopy(records)
                first(altered)["info"]["sourceLink"] = value
                api.render(altered, api.SOURCE, sources)
        row = records["StableRange.RowKernel"]["declarations"][0]
        row["info"]["sourceLink"] = row["info"]["sourceLink"].replace(
            "/StableRange/RowKernel.lean", "/tests/RowKernel.lean")
        with self.assertRaises(ValueError):
            api.render(records, api.SOURCE, sources)
        for line in (0, -1, 1000000, "1", True, first(records)["info"]["line"] + 1):
            with self.subTest(line=line), self.assertRaises(ValueError):
                altered = copy.deepcopy(fixture()[0])
                first(altered)["info"]["line"] = line
                api.render(altered, api.SOURCE, sources)
        name = first(fixture()[0])["info"]["name"]
        for end_line in (0, 1000000, api.EXPECTED[name]["end_line"] + 1):
            with self.subTest(end_line=end_line), self.assertRaises(ValueError):
                altered = copy.deepcopy(api.EXPECTED)
                altered[name]["end_line"] = end_line
                with mock.patch.object(api, "EXPECTED", altered):
                    api.render(fixture()[0], api.SOURCE, sources)
        altered = copy.deepcopy(api.EXPECTED)
        altered[name]["position"] = altered[name]["position"] + 1
        with mock.patch.object(api, "EXPECTED", altered), self.assertRaises(ValueError):
            api.render(fixture()[0], api.SOURCE, sources)
        for revision in ("main", "a" * 39, "A" * 40, "b" * 40):
            with self.subTest(revision=revision), self.assertRaises(ValueError):
                api.render(fixture()[0], revision, fixture()[1])

    def test_manifest_source_pin_and_tool_binding(self):
        records, sources = fixture()
        _, raw = api.render(records, api.SOURCE, sources)
        manifest = json.loads(raw)
        api.manifest_source_binding(manifest, api.SOURCE, sources, records)
        for field, changed in (("format", 2), ("format", True),
                               ("docgen_revision", "b" * 40),
                               ("docgen_tree", "b" * 40),
                               ("docgen_manifest_sha256", "b" * 64),
                               ("docgen_executable_sha256", "b" * 64),
                               ("analyzed_source_tree", "b" * 40),
                               ("analyzed_source_revision", "b" * 40),
                               ("modules", list(api.MODULES[:-1])),
                               ("module_paths", {}), ("inputs", {}),
                               ("documentation_inputs", {}),
                               ("generation_commands", []),
                               ("native_range_binding", {}),
                               ("generation_environment", {})):
            with self.subTest(field=field), self.assertRaises(ValueError):
                api.manifest_source_binding(dict(manifest, **{field: changed}),
                                            api.SOURCE, sources, records)
        for path in api.INPUTS:
            with self.subTest(path=path), self.assertRaises(ValueError):
                api.manifest_source_binding(manifest, api.SOURCE,
                                            dict(sources, **{path: b"changed"}), records)

    def test_portable_parentless_fallback_and_stale_files(self):
        with tempfile.TemporaryDirectory(prefix="stable-api-portable-") as temporary:
            root = Path(temporary)
            records, sources = fixture()
            for path in api.INPUTS + api.DOCUMENTATION_INPUTS + (
                "docs/API.md", "docs/api-manifest.json"):
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                if path in sources:
                    target.write_bytes(sources[path])
                else:
                    shutil.copyfile(ROOT / path, target)
            native = root / "native"
            native.mkdir()
            for module, record in records.items():
                (native / ("declaration-data-" + module + ".bmp")).write_text(
                    json.dumps(record, ensure_ascii=False))
            source_inputs = {path: (root / path).read_bytes() for path in api.INPUTS}
            synthetic_api, synthetic_manifest = api.render(records, api.SOURCE, source_inputs)
            (root / "docs/API.md").write_bytes(synthetic_api)
            (root / "docs/api-manifest.json").write_bytes(synthetic_manifest)
            command = ["python3", "-B", str(root / "scripts/generate_api.py"),
                       "--native-data", str(native), "--source-revision", api.SOURCE]
            def run(*extra):
                return subprocess.run(command + list(extra), capture_output=True, text=True,
                                      cwd=root)
            self.assertEqual(run().returncode, 0)
            self.assertEqual(run("--check").returncode, 0)
            baseline_manifest = (root / "docs/api-manifest.json").read_bytes()
            for path in api.INPUTS:
                original = (root / path).read_bytes()
                (root / path).write_bytes(original + b"drift")
                with self.subTest(source_or_pin=path):
                    self.assertNotEqual(run("--check").returncode, 0)
                (root / path).write_bytes(original)
            self.assertEqual(run("--check").returncode, 0)
            for path in ("README.md", "docs/README.md", "docs/CREDITS.md"):
                original = (root / path).read_bytes()
                (root / path).write_bytes(original + b"stale documentation")
                with self.subTest(documentation=path):
                    self.assertNotEqual(run("--check").returncode, 0)
                (root / path).write_bytes(original)
            (root / "docs/api-manifest.json").write_bytes(baseline_manifest.replace(
                api.TOOL.encode(), b"b" * 40))
            self.assertNotEqual(run("--check").returncode, 0)
            (root / "docs/api-manifest.json").write_bytes(baseline_manifest)
            (root / ".git").write_text("broken Git marker\n")
            self.assertNotEqual(run("--check").returncode, 0)
            (root / ".git").unlink()
            self.assertEqual(run("--check").returncode, 0)
            (root / "docs/API.md").write_bytes(b"stale API\n")
            self.assertNotEqual(run("--check").returncode, 0)

    def test_git_object_probe_and_noncommit_rejection(self):
        with tempfile.TemporaryDirectory(prefix="stable-api-git-") as temporary:
            root = Path(temporary)
            self.assertFalse(api.git_source_available(root, api.SOURCE))
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            self.assertFalse(api.git_source_available(root, api.SOURCE))
            tree = subprocess.check_output(["git", "-C", str(root), "mktree"],
                                           input=b"").decode().strip()
            with self.assertRaisesRegex(ValueError, "not a commit"):
                api.git_source_available(root, tree)


if __name__ == "__main__":
    unittest.main()
