# types

```hs
data AladdinToken smallid
    = AT_keyword String SLoc
    | AT_smallid smallid SLoc
    | AT_largeid String SLoc
    | AT_nat_lit Integer SLoc
    | AT_chr_lit Char SLoc
    | AT_str_lit String SLoc
```

# procedure to analyze

1. lexing

2. preprocess

3. parsing

- inputs: ``aladdin_src :: String``, ``lexical_env :: Map.Map String (Fixity, Precedence)``.

- outputs: ``aladdin_ast :: Either TermRep [DeclRep]``, ``updated_lexical_env :: Map.Map String (Fixity, Precedence)``.

- effects: ``ExceptT ErrMsg``.

# lexing

- inputs: `` aladdin_src :: String``.

- outputs: ``aladdin_tokens_with_string_as_smallid :: [AladdinToken String]``.

- effects: ``ExceptT ErrMsg``.

# preprocess

- inputs: ``aladdin_tokens_with_string_as_smallid :: [AladdinToken String]``, ``lexical_env :: Map.Map String (Fixity, Precedence)``.

- outputs: ``aladdin_tokens_with_augmented_string_as_smallid :: [AladdinToken ((Fixity, Precedence), String)]``, ``updated_lexical_env :: Map.Map String (Fixity, Precedence)``.

- effects: ``ExceptT ErrMsg``.

# parsing

- inputs: ``aladdin_tokens_with_augmented_string_as_smallid :: [AladdinToken ((Fixity, Precedence), String)]``.

- outputs: ``aladdin_ast :: Either TermRep [DeclRep]``.

- effects: ``ExceptT ErrMsg``.
