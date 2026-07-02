# Artifact Abstract

## 1. Paper title

**TBD:** ProofPulse

Replace this placeholder with the exact accepted paper title before submission.

## 2. Link to the accepted paper

**TBD:** add the accepted-paper URL or DOI here.

The paper should be accessible to reviewers during artifact evaluation.

## 3. Purpose

ProofPulse is a Dafny proof-dependency and coverage analysis tool. It parses prover logs, constructs a proof graph, computes line-level coverage, and presents the result in a browser viewer and a VS Code extension. The artifact supports the paper’s claims about proof coverage analysis, diagnosis of weak proofs, and the effect of unsat-core minimization on coverage attribution.

## 4. Badge

The artifact is being submitted for the following badges:

* **Available**: the artifact is packaged for archival distribution and intended for public DOI-based hosting.
* **Reusable**: the repository includes the executable toolchain, benchmark scripts, demo inputs, and documentation needed to understand and repurpose the artifact.
* **Functional**: the artifact is documented, consistent, complete, exercisable, and includes verification and validation evidence through the smoke test, demo workflow, and benchmark workflow.

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