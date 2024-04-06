#import "@preview/polylux:0.3.1": *
#import "@preview/ctheorems:1.1.2": *

#import themes.simple: *

#show: simple-theme.with(
  footer: [],
)

#set par(justify:true)

#title-slide[
  = Banachi ruumi ühikkera plastilisus ning mõned seotud tulemused
  #v(2em)
  Kaarel August Kurik
]

#slide[
  = Meetrilise ruumi plastilisus

  *Definitsioon:* Meetriline ruum $(M,d)$ on _(homöomorfselt) plastiline_ siis, kui
  iga 1‑Lipschitz (homöomorfne) bijektsioon $f : M -> M$ on isomeetria.

  (Panna tähele, et plastilisusest järeldub homöomorfne plastilisus.)


  *Küsimus:* Kas iga Banachi ruumi kinnine ühikkera on plastiline?

  Praegune seis: tõestatud mitmel erijuhul. Peamine võte on ekstremaalsete punktide uurimine.

  *Definitsioon:* Konveksse hulga punkt on _ekstremaalne_ kui hulgas asuvad sirglõigud sisaldavad seda punkti vaid otspunktina.

  Näiteks konveksse hulknurga ekstremaalsete punktide hulk on täpselt tema nurgad, ringi ekstremaalsed punktid ühtivad tema piirjoonega.

  *Definitsioon:* Banachi ruum on _rangelt konveksne_ kui tema ühikkera ekstremaalsete punktide hulk ühtib ühiksfääriga.
]

#slide[
  = Varasemad tulemused

- ruumid, mille ühikkera on ühend lõplikumõõtmelistest polüeedrilistest ekstremaalsetest alamhulkadest (sh kõik rangelt konvekssed Banachi ruumid) @angosto:2019 @cascales:2016,
- mistahes $ell_1$-summa rangelt konvekssetest Banachi ruumidest  (sh $ell_1$ ise) @kadets_zavarzina:2016 @kadets_zavarzina:2018,
- $ell_infinity$-summa *kahest* rangelt konvekssest Banachi ruumist @haller:2022,
- $ell_1 plus.circle_2 RR$ @haller:2022,
- $C(K)$, kus $K$ on kompaktne metriseeruv ruum lõpliku kuhjumispunktide hulgaga (sh $c tilde.equiv C(omega+1)$, ehk koonduvate reaaljadade ruum) @fakhoury:2024 @leo:2022.
]

#slide[
  = Minu tulemused

  1. Kui Banachi ruumi kõik separaablid alamruumid on homöomorfselt plastilise ühikkeraga, siis ruum ise on homöomorfselt plastilise ühikkeraga.

  + Kui iga Banachi ruumi $X$ ühikkera on plastiline, siis kõik 1‑Lipschitz bijektsioonid kujul $f : B_Y -> B_Z$, kus $Y,Z$ on Banachi ruumid, on isomeetriad.

  Need tulemused saab kätte otsese konstruktsiooniga.
]

#slide[
   3. Olgu $X$ rangelt konvekssete Banachi ruumide $X_i$ lõpliku pere $ell_infinity$‑summa. Iga mitteahendav funktsioon $g : B_X -> B_X$ faktoriseerub "teatud kombel" komponentsfääride kaudu.

  Täpsemalt, $ exists sigma in "perm"_n exists g_i : S_i -> S_sigma(i) forall x in B_X (norm(pi_i x) = 1 => g_i (pi_i x) = pi_sigma(i) G(x)). $

   Üks tagajärg: sellise $X$ korral on iga ekstremaalsust säilitav $1$‑Lipschitz bijektsioon $f : B_X -> B_X$ isomeetria.

   Tõestus on sisuliselt graafiteoreetiline, seega leidub graafiteoreetiline analoog teoreemile.
]

#slide[
  #bibliography("refs.yml")
]