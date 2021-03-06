import static org.junit.Assert.fail;

import org.jmlspecs.utils.JmlAssertionError;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;


public class TestExplosivesJUnit4 {

    static int nb_inconclusive = 0;
    static int nb_fail = 0;

    Explosives e;

    public static void main(String args[]) {
    	String testClass = "TestExplosivesJUnit4";
     	org.junit.runner.JUnitCore.main(testClass);
     }


    private void handleJMLAssertionError(JmlAssertionError e) {
    	if (e.getClass().equals(JmlAssertionError.PreconditionEntry.class)) {
    	    System.out.println("\n INCONCLUSIVE "+(new Exception().getStackTrace()[1].getMethodName())+ "\n\t "+ e.getMessage());
            nb_inconclusive++;}
    else{
	    // test failure	
	    nb_fail++;
	    fail("\n\t" + e.getMessage());	
		}  
    }
	
    
	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		nb_inconclusive = 0;
		nb_fail = 0;
		org.jmlspecs.utils.Utils.useExceptions = true;
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	     System.out.println("\n inconclusive tests: "+nb_inconclusive+" -- failures : "+nb_fail );
	}
	
	@Test
	public void  testSequence_0() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Nitro","Prod_Glycerine");
			e.add_incomp("Prod_Dyna","Prod_Mite");
			e.add_assign("Bat_1","Prod_Dyna");
			e.add_assign("Bat_1","Prod_Nitro");
			e.add_assign("Bat_2","Prod_Mite");
			e.add_assign("Bat_2","Prod_Glycerine");
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}
	
	
	@Test
	public void  testSequence_prop_3() {
		try{
			e=new Explosives();
			e.add_incomp("Proteine_Nitro","Proteine_Glycerine");
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}
	
	@Test
	public void  testSequence_prop_3_2() {
		try{
			e=new Explosives();
			e.add_incomp(null,null);
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}
	
	@Test
	public void  testSequence_prop_4() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Nitro","Prod_Glycerine");
			e.add_incomp("Prod_Dyna","Prod_Mite");
			e.add_assign("bat_1","Prod_Dyna");
			e.add_assign("Pat_1","Prod_Nitro");
			e.add_assign("Bat_2","Psod_Mite");
			e.add_assign("Bat_2","Prod_Glycerine");
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}
	
	@Test
	public void  testSequence_prop_4_2() {
		try{
			e=new Explosives();
			e.add_assign("bat_1","Prod_Dyna");
			e.add_assign(null,"Prod_Nitro");
			e.add_assign("Bat_2","Psod_Mite");
			e.add_assign("Bat_2",null);
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}
	
	@Test
	public void  testSequence_prop_5() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Nitro","Prod_Nitro");
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}
	
	@Test
	public void  testSequence_prop_5_2() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_","Prod_");
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}
	
	
	@Test
	public void  testSequence_prop_7() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Nitro","Prod_Glycerine");
			e.add_incomp("Prod_Dyna","Prod_Mite");
			e.add_assign("Bat_1","Prod_Dyna");
			e.add_assign("Bat_2","Prod_Nitro");
			e.add_assign("Bat_1","Prod_Mite");
			e.add_assign("Bat_2","Prod_Glycerine");
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}
	
	@Test
	public void  testSequence_prop_7_2() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Nitro","Prod_Glycerine");
			e.add_incomp("Prod_Dyna","Prod_Mite");
			e.add_assign("Bat_1","Prod_Dyna");
			e.add_assign("Bat_1","Prod_Nitro");
			e.add_assign("Bat_2","Prod_Mite");
			e.add_assign("Bat_2","Prod_Glycerine");
			e.add_incomp("Prod_Mite","Prod_Glycerine");
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}
	
	@Test
	public void  testSequence_prop_8() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Nitro","Prod_Glycerine");
			e.add_incomp("Prod_Dyna","Prod_Mite");
			e.add_assign("Bat_1","Prod_Dyna");
			e.add_assign("Bat_1","Prod_Nitro");
			e.add_assign("Bat_2","Prod_Mite");
			e.add_assign("Bat_2","Prod_Glycerine");
			e.add_assign("Bat_2","Prod_Glycerine");
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}
	
	@Test
	public void  testSequence_prop_9() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Nitro","Prod_Glycerine");
			e.add_assign("Bat_1","Prod_Glycerine");
			e.add_assign("Bat_2","Prod_Glycerine");
			e.add_assign("Bat_3","Prod_Glycerine");
			e.add_assign("Bat_4","Prod_Glycerine");
		} 	catch(JmlAssertionError e){
				handleJMLAssertionError(e);		
		}  
	}


}
