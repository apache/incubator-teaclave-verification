[![Build Status](https://travis-ci.com/apache/incubator-teaclave-verification.svg?branch=master)](https://travis-ci.com/apache/incubator-teaclave-verification)

# Teaclave Verification

This repository contains formal descriptions, specifications, and proofs for Teaclave.

## [`access_control_module`](access_control_module/)

This directory contains formal description and verification of access control 
module of Teaclave described in [`access-control.md`][0]. It uses [`security 
functional requirements`][1] to restate the design specifications, then proves 
the required security objectives in [`Isabelle`][2].

  [0]: https://github.com/apache/incubator-teaclave/blob/master/docs/access-control.md
  [1]: https://www.commoncriteriaportal.org/files/ccfiles/CCPART2V3.1R5.pdf
  [2]: https://isabelle.in.tum.de/index.html

### security problem definition

The purpose of security problem definition is to identify the scope of problems to be 
solved by the access control module. The security problem of access control module of 
Teaclave is defined in terms of the assets protected by the module, the threats encountered 
by the module and the preconditions assumed to be true to the module. 

  * Assets: the confidentiality and integrity of critical data operated by the tasks 
  and functions defined by Teaclave
  
  * Threats: runtime tasks and functions abuse which compromise the confidentiality 
  and integrity of critical data.

  * Assumptions: the critical data can only be accessed through tasks and functions 
  defined by Teaclave; the identification and authentication of users is achieved by 
  the other modules of Teaclave.

### security objectives

The security objective of access control module is to prevent unauthorized users from 
accessing the critical data through tasks and functions. By achieving the security 
objective, the threats of runtime tasks and functions abuse are eliminated under the 
assumptions identified in security problem definition.

### security requirements

Security functional requirements of [`Common Criteria`][3] are used for decomposing 
security objectives with standardized language. The security objective of Teaclave 
access control module is decomposed as follows: 

  * FIA_UAU.2 User authentication before any action <br>
  Dependencies：FIA_UID.1 timing of identification
  
    * FIA_UAU.2.1 The Teaclave access control module shall require each user to be 
    successfully authenticated before allowing any other Teaclave-mediated actions on 
    behalf of that user. *(This requirement is already covered by assumption, so it is 
    not formalized.)*

  * FIA_UID.2 User identification before any action <br>
  Dependencies：No dependencies
  
    * FIA_UID.2.1 The Teaclave access control module shall require each user to be 
    successfully identified before allowing any other Teaclave-mediated actions on 
    behalf of that user. *(This requirement is already covered by assumption, so it 
    is not formalized.)*
  
  * FIA_UAU.3 Unforgeable authentication <br>
  Dependencies：No dependencies
  
    * FIA_UAU.3.1 The Teaclave access control module shall prevent use of authentication 
    data that has been forged by any user of the Teaclave access control module. *(This 
    requirement is already covered by assumption, so it is not formalized.)* 
  
    * FIA_UAU.3.2 The Teaclave access control module shall prevent use of authentication 
    data that has been copied from any other user of the Teaclave access control module. 
    *(This requirement is already covered by assumption, so it is not formalized.)* 
  
  * FIA_USB.1 User-subject binding <br>
  Dependencies：FIA_ATD.1 User attribute definition
  
    * FIA_USB.1.1 The Teaclave access control module shall associate the following user 
    security attributes with subjects acting on the behalf of that user: UsrId. 
  
    * FIA_USB.1.2 The Teaclave access control module shall enforce the following rules on 
    the initial association of user security attributes with subjects acting on the behalf 
    of users: UsrId is in the participants of subjects. 
  
    * FIA_USB.1.3 The Teaclave access control module shall enforce the following rules 
    governing changes to the user security attributes associated with subjects acting on the 
    behalf of users: None.
  
  * FIA_ATD.1 User attribute definition <br>
  Dependencies：No dependencies 
  
    * FIA_ATD.1 The Teaclave access control module shall maintain the following list of 
    security attributes belonging to individual users: UsrId.
  
  * FDP_ACC.1 Subset access control <br>
  Dependencies：FDP_ACF.1 Security attribute based access control
  
    * FDP_ACC.1.1 The Teaclave access control module shall enforce the Teaclave Subset 
    access control SFP on: <br>
    subject: task, user; <br>
    object: function, data; <br>
    operation: task_access_data, task_access_function, user_access_data, user_access_function. 
  
  * FDP_ACF.1 Security attribute based access control <br>
  Dependencies：FDP_ACC.1 Subset access control；<br>
  FMT_MSA.3：Static attribute initialisation
  
    * FDP_ACF.1.1 The Teaclave access control module shall enforce the Teaclave Subset access 
    control SFP to objects based on the following: <br>
    subject attributes: task_participant; UsrId <br>
    object attributes: function_owner; data_owner.
    
    * FDP_ACF.1.2 The TSF shall enforce the following rules to determine if an operation among 
    controlled subjects and controlled objects is allowed: <br>
    task_access_data is allowed if data_owner is the subset of task_participant; <br>
    task_access_function is allowed if function_owner is the subset of task_participant; <br>
    user_access_data is allowed if UsrId is in data_owner; <br>
    user_access_function is allowed if UsrId is in function_owner.
    
    * FDP_ACF.1.3 The TSF shall explicitly authorize access of subjects to objects based on the 
    following additional rules: NONE. 
    
    * FDP_ACF.1.4 The TSF shall explicitly deny access of subjects to objects based on the 
    following additional rules: NONE.
  
  * FMT_MSA.3 Static attribute initialization <br>
  Dependencies：FMT_MSA.1 Management of security attributes；<br>
  FMT_SMR.1 Security roles
  
    * FMT_MSA.3.1 The Teaclave access control shall enforce the Teaclave Subset access control 
    SFP to provide permissive default values for security attributes that are used to enforce 
    the SFP. 
    
    * FMT_MSA.3.2 The TSF shall not allow the Users to specify alternative initial values to 
    override the default values when an object or information is created.
  
  * FMT_MSA.1 Management of security attributes <br>
  Dependencies：FDP_IFC.1 Subset information flow control；<br>
  FMT_SMR.1 Security roles；<br>
  FMT_SMF.1 Specification of Management Functions
  
    * FMT_MSA.1.1 The Teaclave access control module shall enforce the Teaclave Subset access 
    control SFP to restrict the ability to query the security attributes to Users. 
  
  * FMT_SMR.1 Security roles <br>
  Dependencies：FIA_UID.1 Timing of identification
  
    * FMT_SMR.1.1 The Teaclave access control module shall maintain the roles: User. 
      
    * FMT_SMR.1.2 The Teaclave access control module shall be able to associate users with roles.
  
  * FMT_SMF.1 Specification of Management Functions <br>
  Dependencies：No dependencies
  
    * FMT_SMF.1.1 The Teaclave access control module shall be capable of performing the following 
    management functions: <br>
    request_user_access_data, request_user_access_function, request_task_access_data, 
    request_task_access_function, request_user_access_task. 
  
Each security functional requirement listed above is formalized and located in different files. For more information,
please refer to [`access control module introduction`](access_control_module/README.md).

  [3]: https://www.commoncriteriaportal.org/files/ccfiles/CCPART2V3.1R5.pdf
