# portfolio

- 이 레포지토리는 제 작업들의 통합본입니다. This repository is the integration of my works.

# LGS/PGS

- 하스켈 코드를 출력하는 렉서 생성기와 파서 생성기입니다. This contains my lexer generator and my parser generator, both of which print Haskell code.

- 오세만 교수님의 저서 `컴파일러 입문`을 읽고 만들었습니다. I acquire techniques required to have made those generators, reading the book `컴파일러 입문` written by Professor Seman Oh.

- 렉서 생성기는 lookahead operator `/`를 지원하며, 파서 생성기는 LALR(1)의 파서를 생성합니다. This lexer generator supports the positive lookahead operator `/`, and this parser generator yields parsers of LALR(1).

# Aladdin

- 논리형 언어 λProlog의 서브셋입니다. This is a subset of λProlog.

- Xiaochu Qi님의 논문 `An Implementation of the Language Lambda Prolog Organized around Higher-Order Pattern Unification`을 읽고 만들었습니다. Referring the paper `An Implementation of the Language Lambda Prolog Organized around Higher-Order Pattern Unification` of Xiaochu Qi, I made the Aladdin interprerter.

- 이 언어로 `ndc.aladdin`처럼 자연 연역을 검증하는 프로그램을 구현할 수 있습니다. One can write an Aladdin code, which checks natural deduction, such as `ndc.aladdin`.

# A report on the propositional logic

- 명제논리의 건전성과 완전성 그리고 컴팩트성에 대한 증명입니다. 가정한 공리는 `exclusive_middle : forall P : Prop, P \/ ~ P` 뿐입니다. This contains a proof of the propositional soundness theorem, a proof of the propositional completeness theorem, and a proof of the propositional compactness theorem, while only used is the axiom `exclusive_middle : forall P : Prop, P \/ ~ P`.

- 완전성 정리를 증명할 때, Danko Ilik님의 논문 `Constructive Completeness Proofs and Delimited Control`을 참고하였습니다. Referring the paper `Constructive Completeness Proofs and Delimited Control` of Danko Ilik, I proved the propositional completeness theorem.

- 손태승( https://github.com/paulsohn )님께서 비형식적 아이디어를 주시고, 장준영( https://github.com/Ailrun )님께서 Coq 다루는 법을 알려주셨습니다. 두 분께 감사의 말씀을 드립니다. Paul Sohn and Clare Jang teached me how to prove them informally and teached me how to prove with the Coq proof assistant, respectively. Thanks to both.
