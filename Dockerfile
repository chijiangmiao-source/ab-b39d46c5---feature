FROM node:20-alpine

WORKDIR /app

# 零运行时依赖：仅复制源码与测试
COPY package.json ./
COPY src ./src
COPY web ./web
COPY test ./test

ENV NODE_ENV=production \
    HOST=0.0.0.0 \
    PORT=8080

EXPOSE 8080

CMD ["node", "src/server.mjs"]
