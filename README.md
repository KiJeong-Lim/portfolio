# portfolio

- 이 레포지토리는 제 작업들의 통합본입니다.

# LGS/PGS

- 렉서 생성기와 파서 생성기입니다.

- 오세만 교수님의 저서 `컴파일러 입문`을 읽고 만들었습니다.

- 렉서 생성기는 lookahead operator `/`를 지원하며, 파서 생성기는 LALR(1)의 파서를 생성합니다.

# A report on the propositional logic

- 명제논리의 건전성과 완전성 그리고 컴팩트성에 대한 증명입니다. 가정한 공리는 `exclusive_middle : forall P : Prop, P \/ ~ P` 뿐입니다.

- 완전성 정리를 증명할 때, Danko Ilik님의 논문 `Constructive Completeness Proofs and Delimited Control`을 참고하였습니다.

- 손태승( https://github.com/paulsohn )님께서 비형식적 아이디어를 주시고, 장준영( https://github.com/Ailrun )님께서 Coq 다루는 법을 알려주셨습니다. 두 분께 감사의 말씀을 드립니다.

# Aladdin

- 논리형 언어 λ-Prolog의 서브셋입니다.

- Xiaochu Qi님의 논문 `An Implementation of the Language Lambda Prolog Organized around Higher-Order Pattern Unification`을 읽고 만들었습니다.

- 이 언어로 `ndc.aladdin`과 같이 자연 연역을 검증하는 프로그램을 구현할 수 있습니다.

# Butterfly

- 느긋한 순수 함수형 언어입니다.

- Simon Loftus Peyton Jones님과 David Lester님의 출판물 `Implementing functional languages: a tutorial`을 읽고 만들었습니다.

- 소스 파일에 있는 람다식은 lift되지만, repl에 친 람다식은 그대로 람다식입니다.
