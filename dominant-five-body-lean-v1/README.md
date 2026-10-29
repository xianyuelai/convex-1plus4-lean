# Dominant Five Body · v1

本目录是以 `source/convex_1plus4.tex` 和同名 PDF 为权威底本的 v1。源文件身份固定在 [VERSION.json](VERSION.json)，逐项数学对应见 [docs/FULL_ASSERTIONS.json](docs/FULL_ASSERTIONS.json)。旧名 `dominant_five_body_ARMA_rewritten.*`、旧审计和旧验收记录保留为历史材料，不决定 v1 的验收结果。

v1 是否通过整篇验收，由当前 `logs/PAPER_ACCEPTANCE.json` 的 `version=v1`、`paper_verified=true`、源身份和全部文件哈希共同判定。本说明不预填本轮结果；单模块编译、账本中的 VERIFIED 和历史成功记录均不能代替这项判定。交付状态与证据入口见 [FINAL_REPORT.md](FINAL_REPORT.md) 和 [docs/VERIFICATION_SCOPE.md](docs/VERIFICATION_SCOPE.md)。

## 权威源与版本

- TeX：`source/convex_1plus4.tex`，SHA256 `7EA6C309533C233C1BDD5B6C4BDD0BD8DB7374248699FDFD64AD63C124DD6C02`。
- PDF：`source/convex_1plus4.pdf`，19 页，SHA256 `E9A3B8EFBFD5264CF6C988A5276860988E237F4CFFC607F7AB989B879B12D0FF`。
- `logs/SOURCE_BINDING.json` 记录来源副本、隔离重编译及整篇 layout 文本对照。该对照说明 TeX 与 PDF 的内容对应，不认证数学结论。
- v1 通过验收后冻结。未来修改在独立 v2 目录或独立发布版本进行，保留 v1 的源文件、验收记录和 ZIP。具体规则见 [docs/V1_RELEASE.md](docs/V1_RELEASE.md)。

## 锁定环境与复现

使用已经准备好的 Lean/Lake `leanprover/lean4:v4.33.1`，以及 `lake-manifest.json` 中锁定的依赖。mathlib revision 为 `0df444a360eaa60ab8c11dca51a86af692955474`；全部九个 Git 依赖的实际 revision 由验收脚本核对。需要已有 Git、Python 3、PowerShell 7 和相同版本的依赖缓存。

在项目根目录运行：

```powershell
pwsh -NoProfile -File scripts/verify_paper.ps1 -Clean
```

这条命令使用现成环境，不负责安装或更新依赖。不要运行 `lake update`，也不要用不同依赖版本的成功结果替代本版本记录。ZIP 排除本机 `.lake` 缓存，接收方需自行提供锁定版本的环境。

`-Clean` 清理并重建本项目产物，复用锁定依赖；编译持共享锁并限制线程。验收包含完整类型回放、定义值核对、全项目公理依赖审计及 `leanchecker --fresh Audit`、`--fresh PaperAcceptance`。fresh replay 使用同一 Lean 内核，不是第二套独立实现的内核。

日常开发可运行 `pwsh -NoProfile -File scripts/verify.ps1`；单模块使用 `scripts/lean_checked.ps1`。开发验收与整篇源覆盖分别记录，不互相替代。

## 发布与入口

最终验收成功且文件仍与记录一致后，先作只读检查，再打包：

```powershell
python -I -X utf8 scripts/package_project.py --check
python -I -X utf8 scripts/package_project.py
```

打包入口拒绝过期、缺失或不匹配的记录；输出上级目录中的 `dominant-five-body-lean-v1.zip`、同名 `.zip.sha256` 和工程内的 `DELIVERY.json`。交付清单绑定 v1、权威源身份和验收记录。

- `DominantFiveBody/Specification.lean`：统一阈值主规格。
- `DominantFiveBody/Main.lean`：主定理的证明入口。
- `DominantFiveBody/Definitions.lean`：几何、中心构型、相似与真实 Hessian 定义。
- `PaperAcceptance/Main.lean`：展开主规格和定义的独立验收目标。
- `PaperAcceptance/Coverage.lean`：由新稿账本和定义绑定生成的逐项类型回放。
- `PROOF_PACKAGE.md`：证明结构及证据边界。

`.gitattributes` 使用 `* -text` 禁止 checkout 时自动转换换行；验收比较原始字节。未添加授权协议；文献、Lean、mathlib 及其依赖各自原有的权利声明仍适用。