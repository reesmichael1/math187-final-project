set Dishes;
set Days;
set Meals;

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
param weightCalories >= 0;
param reqProtein >= 0;
param weightProtein >= 0;
param reqFiber >= 0;
param weightFiber >= 0;
param reqCarbs >= 0;
param weightCarbs >= 0;
param reqFat >= 0;
param weightFat >= 0;
param reqSatFat >= 0;
param weightSatFat >= 0;
param reqUnsatFat >= 0;
param weightUnsatFat >= 0;
param reqSodium >= 0;
param weightSodium >= 0;
param MAX_SERVED >= 0;
param MAX_PER_DAY >= 0;

var pCalPlus >= 0;
var pCalMinus >= 0;
var pProtPlus >= 0;
var pProtMinus >= 0;
var pFibPlus >= 0;
var pFibMinus >= 0;
var pCarbsPlus >= 0;
var pCarbsMinus >= 0;
var pFatPlus >= 0;
var pFatMinus >= 0;
var pSatFatPlus >= 0;
var pSatFatMinus >= 0;
var pUnsatFatPlus >= 0;
var pUnsatFatMinus >= 0;
var pSodPlus >= 0;
var pSodMinus >= 0;
var fat{Dishes} >= 0;

var amountToServe{Dishes, Days, Meals} >= 0 integer;

minimize Differences:
    weightCalories * (pCalPlus + pCalMinus) + weightProtein * (pProtPlus + pProtMinus)
    + weightFiber * (pFibPlus + pFibMinus) + weightCarbs * (pCarbsPlus + pCarbsMinus)
    + weightFat * (pFatPlus + pFatMinus) + weightSatFat * (pSatFatPlus + pSatFatMinus)
    + weightUnsatFat * (pUnsatFatPlus + pUnsatFatMinus) + weightSodium * (pSodPlus + pSodMinus);

subject to SnackFoodForSnacks{dish in Dishes, day in Days}:
    amountToServe[dish, day, 'Snack'] <= snack[dish];

subject to LunchFoodForLunch{dish in Dishes, day in Days}:
    amountToServe[dish, day, 'Lunch'] <= lunch[dish];

subject to BreakfastFoodForBreakfast{dish in Dishes, day in Days}:
    amountToServe[dish, day, 'Breakfast'] <= breakfast[dish];

subject to DinnerFoodForDinner{dish in Dishes, day in Days}:
    amountToServe[dish, day, 'Dinner'] <= dinner[dish];

subject to NoMoreThanMax{dish in Dishes}:
    sum{day in Days, meal in Meals} amountToServe[dish, day, meal] <= MAX_SERVED;

subject to OnlyOncePerDay{dish in Dishes, day in Days}:
    sum{meal in Meals} amountToServe[dish, day, meal] <= MAX_PER_DAY;

subject to ThreeMealsPerDay{day in Days, meal in Meals}:
    sum{dish in Dishes} amountToServe[dish, day, meal] >= 1;

subject to FatDefinition{dish in Dishes, meal in Meals}:
    fat[dish] = satFat[dish] + unsatFat[dish];

subject to pCalPlusDefinition{day in Days}:
    pCalPlus >= sum{dish in Dishes, meal in Meals}(calories[dish] * amountToServe[dish, day, meal]) - reqCalories;

subject to pCalMinusDefinition{day in Days}:
    pCalMinus >= reqCalories - sum{dish in Dishes, meal in Meals}(calories[dish] * amountToServe[dish, day, meal]);

subject to pProtPlusDefinition{day in Days}:
    pProtPlus >= sum{dish in Dishes, meal in Meals}(protein[dish] * amountToServe[dish, day, meal]) - reqProtein;

subject to pProtMinusDefinition{day in Days}:
    pProtPlus >= reqProtein - sum{dish in Dishes, meal in Meals}(protein[dish] * amountToServe[dish, day, meal]);

subject to pFibPlusDefinition{day in Days}:
    pFibPlus >= sum{dish in Dishes, meal in Meals}(fiber[dish] * amountToServe[dish, day, meal]) - reqFiber;

subject to pFibMinusDefinition{day in Days}:
    pFibMinus >= reqFiber - sum{dish in Dishes, meal in Meals}(fiber[dish] * amountToServe[dish, day, meal]);

subject to pCarbsPlusDefinition{day in Days}:
    pCarbsPlus >= sum{dish in Dishes, meal in Meals}(carbs[dish] * amountToServe[dish, day, meal]) - reqCarbs;

subject to pCarbsMinusDefinition{day in Days}:
    pCarbsMinus >= reqCarbs - sum{dish in Dishes, meal in Meals}(carbs[dish] * amountToServe[dish, day, meal]);

subject to pSodPlusDefinition{day in Days}:
    pSodPlus >= sum{dish in Dishes, meal in Meals}(sodium[dish] * amountToServe[dish, day, meal]) - reqSodium;

subject to pSodMinusDefinition{day in Days}:
    pSodMinus >= reqSodium - sum{dish in Dishes, meal in Meals}(sodium[dish] * amountToServe[dish, day, meal]);

subject to pFatPlusDefinition{day in Days}:
    pFatPlus >= sum{dish in Dishes, meal in Meals}(fat[dish] * amountToServe[dish, day, meal]) - reqFat;

subject to pFatMinusDefinition{day in Days}:
    pFatMinus >= reqFat - sum{dish in Dishes, meal in Meals}(fat[dish] * amountToServe[dish, day, meal]);

subject to pSatFatPlusDefinition{day in Days}:
    pSatFatPlus >= sum{dish in Dishes, meal in Meals}(satFat[dish] * amountToServe[dish, day, meal]) - reqSatFat;

subject to pSatFatMinusDefinition{day in Days}:
    pSatFatMinus >= reqSatFat - sum{dish in Dishes, meal in Meals}(satFat[dish] * amountToServe[dish, day, meal]);

subject to pUnsatFatPlusDefinition{day in Days}:
    pUnsatFatPlus >= sum{dish in Dishes, meal in Meals}(unsatFat[dish] * amountToServe[dish, day, meal]) - reqUnsatFat;

subject to pUnsatFatMinusDefinition{day in Days}:
    pUnsatFatMinus >= reqUnsatFat - sum{dish in Dishes, meal in Meals}(unsatFat[dish] * amountToServe[dish, day, meal]);
