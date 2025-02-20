# 情報数理科学演習I - Lean 4 授業用リポジトリ

このリポジトリは、情報数理演習Iの授業のプリントの証明問題をLean 4で書いたものです。

## 配布ファイル

pdfproofのフォルダの下にLeanのコードがあります。
lakefile.leanやlean-toolchainも含まれています。

## Lean Copilotの使用について

本リポジトリでは、**Lean Copilot**を使用するために、Lean 4.16.0の環境で実行できるように`lakefile.lean`と`lean-toolchain`が設定されています。Lean Copilotを利用することで、より効率的にLeanのコードを書くことが可能です。Lean Copilotが使えない環境では適宜、lakefile.leanやimport文からのぞいてください。

## プロジェクトのセットアップ

1. 自分のパソコンに直接とりこみたい場合は。ターミナル上でリポジトリをクローンします。GitHUBのアカウントがなくてもクローンはできます。

```bash
git clone https://github.com/kashiwabarakenji/pdfproof.git

## 注意点

- **Lean CopilotはWindowsでは基本的にサポートされていません**。そのため、Windows環境でリポジトリを開いてLean 4のコードを検証する場合、`lakefile.lean`の設定を変更する必要があります。
- MacやLinux環境では、現在の設定でLean Copilotが利用できますが、Windowsユーザーの方は`lakefile.lean`の書き換えを行ってください。import LeanCopilotの部分もコメントアウトするとよいでしょう。

lake buildですべてのファイルがbuildできるようには設定されていません。一部をのぞいて、各ファイルは依存せず、独立にコンパイルできるようになっているので、VS Code内でファイルを開いて、Restart Fileでコンパイルしてください。

## 最近の変更
2025年1月 closure systemからclosure operatorが導けることを証明。
2025年2月 Lean 4.16.0にバージョンアップ。

##大変だった証明 ベスト5
- closure operatorとclosure systemの同値性。lattice-closure.leanなど。
- lexorder.leanの辞書式順序が全順序になることの証明。
- 距離空間 dis.leanの01閉区間の連続関数が距離になっていること。
- 束の分配律の片方から、もう片方を証明する問題。lattice.lean
- 自然数の整除関係が分配束になっていること。lattice.lean

##Leanに関する有用なリンク集

Lean by Example 日本語の情報いろいろ https://lean-ja.github.io/lean-by-example/
Lean 定理の検索 Search https://leansearch.net/
Moogle 定理の検索 https://www.moogle.ai
Lean 4 Web ウェブインターフェース https://live.lean-lang.org
Lean Copilot https://github.com/lean-dojo/LeanCopilot
