# Artifact Abstract

## 1. Paper title

ProofPulse: Interactive Proof Coverage Analysis for Dafny

## 2. Link to the accepted paper

https://ase26-tools-datasets.hotcrp.com/doc/ase26-tools-datasets-paper18.pdf

Note: The paper submitted for the Artifact Evaluation track contains updated results compared to the accepted version. These results will be incorporated into the camera-ready paper. Therefore, it is best to use the paper submitted to the Artifact Evaluation track, as its results match the provided artifact.

## 3. Purpose

ProofPulse is a Dafny proof-dependency and coverage analysis tool. It parses prover logs, constructs a proof graph, computes line-level coverage, and presents the result in a browser viewer and a VS Code extension. The artifact supports the paper’s claims about proof coverage analysis, diagnosis of weak proofs, and the effect of unsat-core minimization on coverage attribution.

## 4. Badge

The artifact is being submitted for the following badges:

* **Available**: the artifact is hosted on a public archival repository with a DOI. The source is also publicly accessible on GitHub (https://github.com/VeriFixer/ProofPulse) under an open-source license.
* **Reusable**: the artifact is structured for repurposing beyond paper reproduction. The core analysis library (`@proofpulse/core`) is a standalone npm package with a clean public API, usable as a library or via CLI on any Dafny program. The architecture is modular (log parser, proof graph, coverage engine) and documented so that each component can be extended or replaced independently. The analysis pipeline is language-agnostic at the graph level — any verification-aware language producing a compatible log format can reuse the coverage engine without modification. The repository includes a full test suite with annotated oracles and YAML snapshot tests, a CI pipeline for automated regression checking, demo examples, benchmark scripts, and a web viewer — all enabling reviewers and future researchers to understand, modify, and extend the tool.
* **Functional**: the artifact is documented (README with getting-started and step-by-step instructions), consistent (results match the paper tables), complete (all paper claims are reproducible), and exercisable (Docker image with smoke test completing in under 10 minutes). It includes verification and validation evidence: a 60+ case test suite under `dataset/tests/` with per-line coverage oracles and full proof-graph snapshot assertions, executed automatically via GitHub Actions CI on every commit.

## 5. Technology

### Assumed reviewer skills

* Basic command-line usage.
* Basic familiarity with Docker.
* Basic familiarity with Dafny verification concepts.
* Basic familiarity with VS Code for the editor integration.

### Hardware and software requirements

* Operating system: Linux is the primary target.
* Architectures: x86-64 and ARM64 are supported.
* GPU: not required.
* Docker 24 or newer is recommended for the review workflow.
* At least 8 GB RAM and roughly 10 GB of free disk space are recommended.

## 6. Provenance

The artifact can be obtained from this repository and its packaged review distribution.

* Source Public repository: https://github.com/VeriFixer/ProofPulse
* Recommended review package: a Docker image archive such as `proofpulse-dev.tar.gz`.
* Persistent archival location: to be provided via DOI in the final submission.

## 7. Instructions

### Getting started

1. Load the provided Docker image archive.

```bash
docker load -i proofpulse-dev.tar.gz
```

2. Start the container.

```bash
docker run -it -p 8080:8080 --entrypoint bash proofpulse-dev
```

Follow the instructions on README.md