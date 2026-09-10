# 情報数理科学演習I - Lean 4 授業用リポジトリ

このリポジトリは、情報数理演習Iの授業のプリントの証明問題をLean 4で書いたものです。

## 配布ファイル

pdfproofのフォルダの下にLeanのコードがあります。
lakefile.leanやlean-toolchainも含まれています。

## 使用する Lean のバージョン

このリポジトリは Lean **4.30.0** と対応する mathlib を使用します。LeanCopilot は Lean の更新に追従する安定版が未提供のため、現在の構成からは外しています。

## プロジェクトのセットアップ

1. 自分のパソコンに直接とりこみたい場合は。ターミナル上でリポジトリをクローンします。GitHUBのアカウントがなくてもクローンはできます。

```bash
git clone https://github.com/kashiwabarakenji/pdfproof.git
cd pdfproof
lake update
lake exe cache get
```

## 注意点

- `lake build Pdfproof.Lattice.lattice` のように、対象モジュールを指定してビルドできます。
- 全ファイルを順に検証するには、次を実行します。

```bash
rg --files Pdfproof -g '*.lean' |
  sed 's#/#.#g; s#\.lean$##' |
  xargs -n 1 lake build
```

lake buildですべてのファイルがbuildできるようには設定されていません。一部をのぞいて、各ファイルは依存せず、独立にコンパイルできるようになっているので、VS Code内でファイルを開いて、Restart Fileでコンパイルしてください。

## 最近の変更
2025年1月 closure systemからclosure operatorが導けることを証明。
2026年9月 Lean 4.30.0 にバージョンアップ。

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
