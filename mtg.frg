#lang forge/froglet

abstract sig Boolean {}
one sig True, False extends Boolean {}

//Players
abstract sig Player {
    lifeTotal: one Int
}
one sig Player1, Player2 extends Player {}

//Cards
abstract sig Card {
    tapped: one Boolean,
    manaCost: one Int
}
sig Creature extends Card {
    attack: one Int,
    health: one Int
}
sig Land extends Card {}

pred cardsWellInit {
    all c: Creature | {
        c.health >= 0
        c.attack >= 0 
    }
    all l: Land | {
        l.manaCost = 0
    }
}

pred wellformedGamestart {
    all p: Player | {
        p.lifeTotal = 20
    }
}

run {cardsWellInit
    wellformedGamestart
} for exactly 5 Card, 2 Player, 6 Int

