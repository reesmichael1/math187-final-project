set Dishes;

param protein{Dishes} >= 0;
param calories{Dishes} >= 0;
param carbs{Dishes} >= 0;
param fiber{Dishes} >= 0;
param sugar{Dishes} >= 0;
param satFat{Dishes} >= 0;
param transFat{Dishes} >= 0;
param unsatFat{Dishes} >= 0;
param vitaminA{Dishes} >= 0;
param vitaminC{Dishes} >= 0;
param vitaminD{Dishes} >= 0;
param vitaminE{Dishes} >= 0;
param vitaminK{Dishes} >= 0;
param sodium{Dishes} >= 0;
param calcium{Dishes} >= 0;
param iron{Dishes} >= 0;
param vegetarian{Dishes} >= 0;
param likedAmount{Dishes} >= -1;
param breakfast{Dishes} >= 0;
param lunch{Dishes} >= 0;
param dinner{Dishes} >= 0;
param snack{Dishes} >= 0;


param reqCalories >= 0;
param weightCalories >- 0;
param reqProtein >= 0;
param weightProtein >= 0;


var pCalPlus >= 0;
var pCalMinus >= 0;
var pProtPlus >= 0;
var pProtMinus >= 0;

var amountToServe{Dishes} >= 0; # or not integer? 

subject to NoMoreThan2{d in Dishes}:
amountToServe[d] <= 2;

subject to pCalPlusDefinition:
pCalPlus >= sum{d in Dishes}(calories[d] * amountToServe[d]) - reqCalories;
subject to pCalMinusDefinition:
pCalMinus >= reqCalories - sum{d in Dishes}(calories[d] * amountToServe[d]);

subject to pProtPlusDefinition:
pProtPlus >= sum{d in Dishes}(protein[d] * amountToServe[d]) - reqProtein;
subject to pProtMinusDefinition:
pProtPlus >= reqProtein - sum{d in Dishes}(protein[d] * amountToServe[d]);

minimize Differences:
weightCalories * (pCalPlus + pCalMinus); #+ weightProtein * (pProtPlus + pProtMinus);
