ARG TOOLCHAIN_IMAGE

# Network-allowed acquisition target. It is not the build payload. A caller
# must inspect the result and may promote it only if its config ID and pinned
# components equal the canonical values checked by the orchestrator.
FROM docker.io/risczero/risc0-guest-builder@sha256:3e12f71bacd27527a61dea96fa0e53e468c99aa261d3a1019b593f6dbd943eb3 AS toolchain
RUN rustup toolchain install 1.96.1 --profile minimal
ENV RUSTUP_TOOLCHAIN=1.96.1

# The payload uses a dedicated local binding whose config ID is verified by
# the orchestrator immediately before and after this build.
FROM ${TOOLCHAIN_IMAGE} AS input

ARG EXPECTED_SOURCE_COMMIT
ARG EXPECTED_SOURCE_MANIFEST_SHA256

LABEL org.opencontainers.image.source="https://github.com/oraclizer/statesync-gkr" \
      io.oraclizer.statesync-gkr.source-commit="${EXPECTED_SOURCE_COMMIT}" \
      io.oraclizer.statesync-gkr.source-manifest-sha256="${EXPECTED_SOURCE_MANIFEST_SHA256}"

WORKDIR /workspace/source

# Only this closed, declared source-input allowlist enters the image. The
# recipe directory is outside the allowlist.
COPY source/Cargo.toml source/Cargo.lock source/rust-toolchain.toml ./
COPY source/src/ ./src/
COPY source/crates/ ./crates/
COPY source/spikes/zkvm-wrap/common/ ./spikes/zkvm-wrap/common/
COPY source/spikes/zkvm-wrap/risc0-host/ ./spikes/zkvm-wrap/risc0-host/
COPY source/spikes/zkvm-wrap/risc0-methods/ ./spikes/zkvm-wrap/risc0-methods/
COPY source/tests/vectors/inner-proof-v1/membership-d24.bin ./tests/vectors/inner-proof-v1/membership-d24.bin

COPY source-manifest.txt /opt/ssgkr/source-manifest.txt
COPY source-content.sha256 /opt/ssgkr/source-content.sha256
COPY source-commit.txt /opt/ssgkr/source-commit.txt
COPY build-guest.sh /usr/local/bin/ssgkr-build-guest

RUN test -n "${EXPECTED_SOURCE_COMMIT}" \
    && test -n "${EXPECTED_SOURCE_MANIFEST_SHA256}" \
    && test "$(cat /opt/ssgkr/source-commit.txt)" = "${EXPECTED_SOURCE_COMMIT}" \
    && echo "${EXPECTED_SOURCE_MANIFEST_SHA256}  /opt/ssgkr/source-manifest.txt" | sha256sum -c - \
    && cd /workspace/source \
    && sha256sum -c /opt/ssgkr/source-content.sha256 \
    && chmod 0555 /usr/local/bin/ssgkr-build-guest

ENTRYPOINT ["/usr/local/bin/ssgkr-build-guest"]
