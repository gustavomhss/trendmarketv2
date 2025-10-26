FROM alpine:3.19.1@sha256:f49f3562f4da4f9c0b42da1cba3aaee47cebb6a2e63a64a6b740249b5b88f0d9

RUN apk add --no-cache bash curl jq python3 py3-pip nodejs npm
WORKDIR /workspace
