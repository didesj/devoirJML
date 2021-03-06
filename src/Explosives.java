// Based on a B specification from Marie-Laure Potet.

public class Explosives{
    public int nb_inc = 0;
    public int histoNbComp = 0;
    public String [][] incomp = new String[50][2];
    public int nb_assign = 0;
    public String [][] assign = new String[30][2];
    
    
    public Explosives() {
		// TODO Auto-generated constructor stub
	}
    /*@ public invariant // Prop 1 : le nombre d'éléments incompatibles doit être compris entre 0 et 50 exclu
      @ (0 <= nb_inc && nb_inc < 50);
      @*/
    /*@ public invariant // Prop 2 : le nombre d'éléments assignés doit être compris entre 0 et 30 exclu
      @ (0 <= nb_assign && nb_assign < 30);
      @*/
    /*@ public invariant // Prop 3 : tous les éléments (type String) dans le double tableau incomp doivent commencer par "Prod"
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @         incomp[i][0].startsWith("Prod") && incomp[i][1].startsWith("Prod"));
      @*/
    /*@ public invariant // Prop 4 :	Tous les String de la première colonne de assign (assign[i][0]) doivent commencer par "Bat"
      @			 // 		Tous les String de la deuxième colonne de assign (assign[i][1]) doivent commencer par "Prod"
      @ (\forall int i; 0 <= i && i < nb_assign; 
      @         assign[i][0].startsWith("Bat") && assign[i][1].startsWith("Prod"));
      @*/
    /*@ public invariant // Prop 5 : Un élément ne peut pas apparaitre incompatible avec lui même dans le tableau incomp
      @ (\forall int i; 0 <= i && i < nb_inc; !(incomp[i][0]).equals(incomp[i][1]));
      @*/

    /*@ public invariant // Prop 6 : Si un élément i apparait incompatible avec un autre j, alors j apparait incompatible à i dans incomp
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @        (\exists int j; 0 <= j && j < nb_inc; 
      @           (incomp[i][0]).equals(incomp[j][1]) 
      @              && (incomp[j][0]).equals(incomp[i][1]))); 
      @*/
    
    /*@ public invariant // Prop 7 : Tous les éléments assignés à un même batiments ne doivent pas être incompatible 2 à 2
      @ (\forall int i; 0 <= i &&  i < nb_assign; 
      @     (\forall int j; 0 <= j && j < nb_assign; 
      @        (i != j && (assign[i][0]).equals(assign [j][0])) ==>
      @        (\forall int k; 0 <= k && k < nb_inc;
      @           (!(assign[i][1]).equals(incomp[k][0])) 
      @              || (!(assign[j][1]).equals(incomp[k][1])))));
      @*/
    
    /*@ public invariant // Prop 8 : Toutes les lignes du tableau des affectations sont différents deux à deux
      @ (\forall int i; 0 <= i &&  i < nb_assign;
      @  	(\forall int j; 0 <= j && j < nb_assign;
      @			(i==j) || !((assign[i][0].equals(assign[j][0])) && (assign[i][1].equals(assign[j][1]))) ));
      @*/
    
    
    /*@ public invariant // Prop 9 : Un produit ne peut pas être stocké dans plus de trois bâtiments
      @ (\forall int i; 0 <= i &&  i < nb_assign;
      @ 		bonStock(assign[i][1]));
      @*/
    
    /*@ public constraint // Prop 10 : Le nombre d'incompatibilités ne peut jamais diminuer
      @		\old(nb_inc)<=nb_inc;
      @*/

    
    public /*@ pure helper @*/  boolean bonStock(String prod){
	    	int compt = 0;
	    	for(int i = 0 ;i < nb_assign;i++){
	    		if(assign[i][1].equals(prod)){
	    			compt ++;
	    		}
	    	}
	    	if(compt >= 3){
	    		return false;
	    	}
	    	return true;	
	}
    
    //@ requires (prod1.startsWith("Prod") && prod2.startsWith("Prod"));
    //@ requires (!prod1.equals(prod2));
    //@ requires !memeBat(prod1,prod2);
    public void add_incomp(String prod1, String prod2){
    		histoNbComp=nb_inc;
		incomp[nb_inc][0] = prod1;
		incomp[nb_inc][1] = prod2;
		incomp[nb_inc+1][1] = prod1;
		incomp[nb_inc+1][0] = prod2;
		nb_inc = nb_inc+2;
     }
    
    //@ requires prod.startsWith("Prod") && bat.startsWith("Bat");
    //@ requires batComp(bat, prod);
    public void add_assign(String bat, String prod){
	assign[nb_assign][0] = bat;
	assign[nb_assign][1] = prod;
	nb_assign = nb_assign+1;
    }
    
    private /*@ spec_public pure helper @*/ boolean memeBat(String prod1, String prod2) {
    		for(int i = 0; i<nb_assign; i++) {
    			if(assign[i][1].equals(prod1)) {
    				for(int j = 0; j<nb_assign; j++) {
    					if(assign[j][0].equals(assign[i][0]) && assign[j][1].equals(prod2)) {
    						return true;
    					}
    				}
    			}
    		}
    		return false;
    }
    
    private /*@ spec_public pure helper @*/ boolean batComp(String bat, String prod) {
    		for(int i = 0; i<nb_assign; i++) {
    			if(assign[i][0].equals(bat) && !compatible(assign[i][1], prod)) {
    				return false;
    			}
    		}
    		return true;
    }
    
    private /*@ spec_public pure helper @*/ boolean compatible(String prod1, String prod2){
    		for(int i = 0; i<nb_inc; i++) {
    			if((incomp[i][0].equals(prod1) || incomp[i][0].equals(prod2)) && ((incomp[i][1].equals(prod1) || incomp[i][1].equals(prod2)))) {
    				return false;
    			}
    		}
    		return true;
    }
    
    //@ ensures \result.startsWith("Bat");
    public String findBat (String prod) {
    		String batCheck[] = new String[30]; // batiments déjà verifié
    		int index = 0;
    		String bat;
    		boolean batAllreadyCheck = false;
    		for(int i = 0; i < nb_assign; i++) {
    			for(int j = 0; j <index; j++) {
    				if(assign[i][0].equals(batCheck[j])) {
    					batAllreadyCheck = true;
    				}
    			}
    			if(!batAllreadyCheck) { // si le batiment n'a pas été encore vérifié
    				bat = assign[i][0];
    				boolean batOk = true;
	    			for(int k = 0; k < nb_assign; k++) {
	    				if(assign[k][0].equals(bat) && !compatible(prod, assign[k][1])) {
	    					batOk = false;
	    				}
	    			}
	    			if(batOk) {
	    				return bat;
	    			}
	    			batCheck[index] = bat;
	    			index++;
    			}
    		}
    		return "Bat_"+prod;
    }
     
    
    public void skip(){
    }
}
