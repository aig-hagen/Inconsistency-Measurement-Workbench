// Example knowledge bases shown in the "Examples" menu.
window.IM_EXAMPLES = [
  {
    name: 'Overlapping conflicts',
    text: `% Three minimal inconsistent subsets sharing formulas
a
!a
b
!b
!a || b
c`,
  },
  {
    name: 'Penguin (default reasoning)',
    text: `% Tweety is a penguin; penguins are birds; birds fly; penguins do not fly
penguin
penguin => bird
bird => flies
penguin => !flies
bird => wings
wings`,
  },
  {
    name: 'Chain of implications',
    text: `% A single minimal inconsistent subset of size 5
a
a => b
b => c
c => d
!d
e => d`,
  },
  {
    name: 'Self-contradiction',
    text: `% A self-contradictory formula: several measures become infinite
a && !a
b
b => c
!c || d`,
  },
  {
    name: 'Medical diagnosis',
    text: `% Conflicting evidence from symptoms and a lab test
fever && cough => flu
fever
cough
test_negative => !flu
test_negative
flu => rest
!rest`,
  },
  {
    name: 'Lottery',
    text: `% Exactly one of three tickets wins, but each is believed to lose
t1 || t2 || t3
!t1
!t2
!t3
t1 => !t2 && !t3`,
  },
  {
    name: 'Disjunctive conflict (Hunter & Konieczny)',
    text: `a
!a
b
!b
a || b`,
  },
  {
    name: 'Equivalences and exclusive or',
    text: `p <=> q
q <=> r
p ^^ r
p
s => (p <=> !s)`,
  },
  {
    name: 'Consistent base',
    text: `% No conflicts: every measure is 0
rain => wet
wet => slippery
rain
!snow`,
  },
  {
    name: 'Pigeonhole (3 pigeons, 2 holes)',
    text: `% Each pigeon sits in a hole; no hole holds two pigeons
p1h1 || p1h2
p2h1 || p2h2
p3h1 || p3h2
!(p1h1 && p2h1)
!(p1h1 && p3h1)
!(p2h1 && p3h1)
!(p1h2 && p2h2)
!(p1h2 && p3h2)
!(p2h2 && p3h2)`,
  },
];
