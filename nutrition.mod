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
param MAX_SERVED >= 0;
param MAX_PER_DAY >= 0;

var pCalPlus >= 0;
var pCalMinus >= 0;
var pProtPlus >= 0;
var pProtMinus >= 0;

var amountToServe{Dishes, Days, Meals} >= 0 integer;

minimize Differences:
    weightCalories * (pCalPlus + pCalMinus); #+ weightProtein * (pProtPlus + pProtMinus);

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

subject to pCalPlusDefinition{day in Days}:
    pCalPlus >= sum{dish in Dishes, meal in Meals}(calories[dish] * amountToServe[dish, day, meal]) - reqCalories;

subject to pCalMinusDefinition{day in Days}:
    pCalMinus >= reqCalories - sum{dish in Dishes, meal in Meals}(calories[dish] * amountToServe[dish, day, meal]);

subject to pProtPlusDefinition{day in Days}:
    pProtPlus >= sum{dish in Dishes, meal in Meals}(protein[dish] * amountToServe[dish, day, meal]) - reqProtein;

subject to pProtMinusDefinition{day in Days}:
    pProtPlus >= reqProtein - sum{dish in Dishes, meal in Melas}(protein[dish] * amountToServe[dish, day, meal]);
