# 情報数理演習I - Lean 4 授業用リポジトリ

このリポジトリは、情報数理演習IのLean 4の授業のために試験的に公開しているものです。主に授業内で使用するLean 4のコードが含まれています。

## Lean Copilotの使用について

本リポジトリでは、**Lean Copilot**を使用するために、Lean 4.11の環境で実行できるように`lakefile.lean`と`lean-toolchain`が設定されています。Lean Copilotを利用することで、より効率的にLeanのコードを書くことが可能です。

### 注意点

- **Lean CopilotはWindowsではサポートされていません**。そのため、Windows環境でリポジトリを開いてLean 4のコードを検証する場合、`lakefile.lean`の設定を変更する必要があります。
- MacやLinux環境では、現在の設定でLean Copilotが利用できますが、Windowsユーザーの方は`lakefile.lean`の書き換えを行ってください。

### プロジェクトのセットアップ

1. リポジトリをクローンします。

```bash
git clone https://github.com/kashiwabarakenji/pdfproof.git