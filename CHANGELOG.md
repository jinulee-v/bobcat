## Changes since 1.2.0

One line per change, be concise and explicit. Document only external changes
in behavior visible for the end-users of the tooling.

* BOBCat now resolves named Catala values to their definitions instead of
  treating constants and named lists as unconstrained Z3 inputs. Unresolved
  internal values and functions are reported as encoding defects.

* [#1058](https://github.com/CatalaLang/catala/pull/1058) Fixes a bug
  in the JSON output format of enumerations yielding errors such as:
  `Invalid_argument("Json_encoding.construct: consequence of non
  exhaustive Json_encoding.string_enum` and
  `Invalid_argument("Json_encoding.construct: consequence of bad
  union")`

* [#1069](https://github.com/CatalaLang/catala/pull/1069) Revamp of
  the `--trace` mechanism:
  - Added support in the `Java` backend;
  - Added `clerk run --trace ...` options.
