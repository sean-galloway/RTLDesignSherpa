# Reference archive for articles

Primary papers and canonical sources that explain techniques used in the articles. Each entry records the specific conceptual role; inclusion is attribution for convergent ideas, not a claim that the implementation began with the source.

File naming: `<Technique>__<FirstAuthor><Year>.pdf`. Downloaded papers are opened and checked against the cited title and author. Books and web sources without a local archival copy retain a publisher, DOI, or author-site link.

## Generic valid/ready BFM collateral in Cocotb

| Technique | Full citation and source | Role in the article | Local copy |
|---|---|---|---|
| Human-first explanation | Donald E. Knuth, "Literate Programming," *The Computer Journal* 27(2), 1984, pp. 97–111. [DOI](https://doi.org/10.1093/comjnl/27.2.97) | Conceptual analogy for generating readable packet diagnostics from the same field description used for execution. It is not a claim that the BFM uses WEB or literate programming. | `LiterateProgramming__Knuth1984.pdf` |
| Table-driven methods | Steve McConnell, *Code Complete*, 2nd ed., Microsoft Press, 2004, Chapter 18, ["Table-Driven Methods"](https://www.oreilly.com/library/view/code-complete-2nd/0735619670/ch18.html) | `FieldConfig` supplies descriptors that drive generic packing, collection, resolution, comparison, and formatting instead of per-interface logic. | Citation and publisher link |
| Adapter and Strategy | Erich Gamma, Richard Helm, Ralph Johnson, and John Vlissides, *Design Patterns: Elements of Reusable Object-Oriented Software*, Addison-Wesley, 1995. [Publisher](https://www.informit.com/store/design-patterns-elements-of-reusable-object-oriented-9780201633610); [Adapter excerpt](https://www.informit.com/articles/article.aspx?p=1398600) | Adapter reconciles the common packet API with different RTL interfaces; Strategy names the interchangeable packed and multi-signal payload implementations. | Citation and publisher links |
| Canonical data model | Gregor Hohpe and Bobby Woolf, *Enterprise Integration Patterns*, Addison-Wesley, 2003, ["Canonical Data Model"](https://www.enterpriseintegrationpatterns.com/patterns/messaging/CanonicalDataModel.html) | `Packet` provides a common transaction representation independent of the RTL's physical payload format. | Citation and author-site link |
| Convention over configuration | David Heinemeier Hansson, ["The Ruby on Rails Doctrine: Convention over Configuration"](https://rubyonrails.org/doctrine) | Common naming heuristics connect conventional interfaces automatically; `signal_map` declares only the exceptions. | Citation and author-site link |
