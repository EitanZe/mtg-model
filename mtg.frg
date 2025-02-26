#lang forge

abstract sig Boolean {}
one sig True, False extends Boolean {}

sig TIME {
    next: lone TIME
}

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

abstract sig Action {
    next: lone Action,
    player: one Player
}
sig playCard extends Action {
    c: lone Card
}
// sig castSpell extends playCard {} //for playing lands vs casting creatures

sig declareAttackers extends Action {
    creatures: set Card
}
sig block extends Action {

}
sig endTurn extends Action {}
sig untap extends Action {}


pred cardsWellInit {
    all c: Creature | {
        c.health >= 0 //max defaults are 0-15
        c.health <= 15
        c.attack >= 0
        c.attack <= 15
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

pred validActionSequence {
    all a: Action | some p1, p2: Player {
        a.player = p1 implies //don't switch players unless
        (a.next.player = p1) or (a.next.player = p2 and (a.next in block or a in endTurn)) //blocking or endTurn

        a in endTurn implies //switch players after endTurn
        a.player != a.next.player
    }
}

run {cardsWellInit
    wellformedGamestart
    validActionSequence
} for exactly 4 Action, 2 endTurn, 6 Int for {next is linear}

