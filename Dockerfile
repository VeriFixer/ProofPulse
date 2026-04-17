FROM node:22-slim

ARG DAFNY_VERSION=4.9.1

RUN apt-get update && apt-get install -y --no-install-recommends \
    wget unzip libicu-dev ca-certificates \
    && rm -rf /var/lib/apt/lists/*

RUN wget -q "https://github.com/dafny-lang/dafny/releases/download/v${DAFNY_VERSION}/dafny-${DAFNY_VERSION}-x64-ubuntu-20.04.zip" \
      -O /tmp/dafny.zip \
    && unzip -q /tmp/dafny.zip -d /opt \
    && rm /tmp/dafny.zip \
    && ln -s /opt/dafny/dafny /usr/local/bin/dafny \
    || (echo "ERROR: Failed to download/install Dafny ${DAFNY_VERSION}" && exit 1)

WORKDIR /app
COPY package.json ./
COPY packages/core/package.json ./packages/core/
COPY packages/core/tsconfig.json ./packages/core/
COPY packages/core/src/ ./packages/core/src/
COPY packages/vscode-extension/package.json ./packages/vscode-extension/
RUN npm install --ignore-scripts
RUN npm run build -w packages/core
COPY src/ ./src/
COPY dataset/ ./dataset/

CMD ["npm", "test"]
