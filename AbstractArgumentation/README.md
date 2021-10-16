# Formalization of Argumentation Frameworks

In this folder, an encoding of Dung-style abstract argumentation frameworks (AFs) into higher-order logic (HOL)
(aka. extensional type theory) is presented.

## File structure

```
.
├── adequacy.thy                --- Proves some exemplary theorems to demonstrate the adequacy of the encoding
├── base.thy                    --- Basic definitions on arguments, extensions, labellings, etc.
├── correspondence.thy          --- Correspondences between labellings and extensions
├── correspondence-simpl.thy    --- Correspondences between labellings and extensions (simplified defs)
├── extensions.thy              --- Extension-based argumentation semantics
├── extensions-simpl.thy        --- Extension-based argumentation semantics (simplified defs)
├── ext-properties.thy          --- Proves some properties of extensions and refutes others
├── ext-relationships.thy       --- Proves inclusion relationships among extensions
├── ext-simpl-properties.thy    --- Proves some properties of extensions and refutes others (simplified defs)
├── labellings.thy              --- Labelling-based argumentation semantics
├── labellings-simpl.thy        --- Labelling-based argumentation semantics (simplified defs)
├── lab-properties.thy          --- Proves some properties of labellings and refutes others
├── lab-relationships.thy       --- Proves inclusion relationships among labellings
├── lab-simpl-properties.thy    --- Proves some properties of labellings and refutes others (simplified defs)
├── misc.thy                    --- Miscellaneous basic definition (sets, relations, orderings, etc.)
├── model-generation.thy        --- Generation of extensions and labellings using Nitpick
├── README.md                   --- This README file
└── Zorn-lemma.thy              --- Useful lemmas concerning orderings (incl. Zorn's)
```
