FROM node:22-slim

ARG DAFNY_VERSION=4.11.0

RUN apt-get update && apt-get install -y --no-install-recommends \
    wget unzip libicu-dev ca-certificates python3 \
    && rm -rf /var/lib/apt/lists/*

RUN wget -q "https://github.com/dafny-lang/dafny/releases/download/v${DAFNY_VERSION}/dafny-${DAFNY_VERSION}-x64-ubuntu-22.04.zip" \
      -O /tmp/dafny.zip \
    && unzip -q /tmp/dafny.zip -d /opt \
    && rm /tmp/dafny.zip \
    && ln -s /opt/dafny/dafny /usr/local/bin/dafny \
    || (echo "ERROR: Failed to download/install Dafny ${DAFNY_VERSION}" && exit 1)

WORKDIR /app

# Copy package manifests first for better layer caching
COPY package.json package-lock.json vitest.config.ts ./
COPY core/package.json core/tsconfig.json ./core/
COPY evaluation/package.json ./evaluation/
COPY vscode_extension/package.json ./vscode_extension/

RUN npm ci --ignore-scripts

# Copy source and build
COPY core/src/ ./core/src/
COPY core/scripts/ ./core/scripts/
COPY web_viewer/ ./web_viewer/
RUN npm run build:core
RUN npm run build:viewer

# Copy everything else needed at runtime
COPY tests/ ./tests/
COPY evaluation/src/ ./evaluation/src/
COPY evaluation/vitest.config.ts ./evaluation/
COPY dataset/ ./dataset/
COPY dafny-synthesis/ ./dafny-synthesis/

CMD ["npm", "run", "test:all"]
