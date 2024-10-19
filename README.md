# 情報数理科学演習I - Lean 4 授業用リポジトリ

このリポジトリは、情報数理演習IのLean 4の授業のために試験的に公開しているものです。主に授業内で使用するLean 4のコードが含まれています。

## 配布ファイル

pdfproofのフォルダの下にLeanのコードがあります。いくつかのテーマごとに分けました。

## Lean Copilotの使用について

本リポジトリでは、**Lean Copilot**を使用するために、Lean 4.11の環境で実行できるように`lakefile.lean`と`lean-toolchain`が設定されています。Lean Copilotを利用することで、より効率的にLeanのコードを書くことが可能です。

## プロジェクトのセットアップ

1. 自分のパソコンに直接tpリコみたい場合は。ターミナル上でリポジトリをクローンします。GitHUBのアカウントがなくてもクローンはできます。

```bash
git clone https://github.com/kashiwabarakenji/pdfproof.git

## 注意点

- **Lean CopilotはWindowsでは基本的にサポートされていません**。そのため、Windows環境でリポジトリを開いてLean 4のコードを検証する場合、`lakefile.lean`の設定を変更する必要があります。
- MacやLinux環境では、現在の設定でLean Copilotが利用できますが、Windowsユーザーの方は`lakefile.lean`の書き換えを行ってください。import LeanCopilotの部分もコメントアウトするとよいでしょう。

##Leanに関する有用なリンク集

Lean by Example 日本語の情報いろいろ https://lean-ja.github.io/lean-by-example/
Lean 定理の検索 Search https://leansearch.net/
Moogle 定理の検索 https://www.moogle.ai
Lean 4 Web ウェブインターフェース https://live.lean-lang.org
Lean Copilot https://github.com/lean-dojo/LeanCopilot
