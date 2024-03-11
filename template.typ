#let project(title: "", authors: (), subject-class: (), 
key-words: (),
body) = {
  // Set the document's basic properties.
  set document(author: authors.map(a => a.name), title: title)

  let footer = locate(loc => {
    align(center, counter(page).display())
    let i = counter(page).at(loc).first();
    if (i == 1) {
      v(0.25em, weak:true)
      line()
      v(0.5em, weak:true)
      if (subject-class.len() > 0) {
      [2020 _Mathematics Subject Classification_. #subject-class.join(", ")]
      }
      v(0.5em, weak:true)
      if (key-words.len() > 0) {
      [_Key words and phrases._ #key-words.join("; ")]
      }
    }
  })

  set page(numbering: "1", number-align: center, footer: footer,
  footer-descent: 30%,
  )
  set text(font: "Linux Libertine", lang: "en")
  set heading(numbering: "1.1.")


  // Title row.
  align(center)[
    #block(text(weight: 700, 1.75em, title))
  ]

  // Author information.
  pad(
    top: 0.5em,
    bottom: 0.5em,
    x: 2em,
    grid(
      columns: (1fr,) * calc.min(3, authors.len()),
      gutter: 1em,
      ..authors.map(author => align(center)[
        *#author.name* \
        #author.email
      ]),
    ),
  )

  // Main body.
  set par(justify: true)

  body

  pad(
    top: 0.5em,
    x: 2em,
    grid(
      columns: (1fr,),
      ..authors.map(author => [
        #smallcaps(author.affiliation) \
        _Email address_: #raw(author.email)
      ])
    )
  )
}