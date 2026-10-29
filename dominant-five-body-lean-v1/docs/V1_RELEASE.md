# v1 发布规则

v1 的权威稿、版本身份和依赖锁定信息保存在 `VERSION.json`。`source/convex_1plus4.tex` 与同名 PDF 是该版本唯一权威稿；旧名稿件、`logs/history/` 与明确标为早期快照的文档用于追溯。

## 冻结顺序

1. 完成新稿语义对应、Lean 修改、发布说明和来源核验。
2. 冻结全部验收输入，运行现有 `scripts/verify_paper.ps1 -Clean`。期间不修改源码、账本、文档、脚本或版本元数据。
3. 仅当当前 v1 receipt 成功且字节仍匹配时，运行 `python -I -X utf8 scripts/package_project.py --check`。
4. 最后运行打包入口，保留 `DELIVERY.json`、上级目录中的 `<工程目录名>.zip` 及 `.zip.sha256`。交付清单记录 v1、权威稿身份、验收 receipt 哈希和逐文件哈希。

本说明不预填本轮检查结果。是否完成以实际 receipt 与哈希核验为准。

## 后续版本

v1 交付完成后，其权威稿、数学源码、账本、依赖锁定配置、验收日志和 ZIP 共同构成冻结快照。后续工作创建独立 v2 目录或独立发布版本，更新版本身份并重新进行源对应和验收。不得用 v2 文件覆盖 v1，或让 v1 的旧成功记录为 v2 背书。

## 字节稳定性

`.gitattributes` 使用 `* -text`，所有文件按字节保存，避免 Git 根据 `core.autocrlf` 转换 LF/CRLF 后改变验收哈希。它不会重写现有文件；任何显式编辑仍须重新验收。ZIP 内每个文件按 `DELIVERY.json` 校验。

不随本发布自动安装／更新 Lean 或依赖，不添加未经用户选择的授权协议。所有已有第三方来源和权利说明保留。