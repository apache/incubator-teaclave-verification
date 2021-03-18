(*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 *)

theory I_FMT_MSA
  imports Main "../FMT_MSA" I_ResrcAttr
begin

datatype SubjAttrConf = nosubjattrconf |
                       is_subjattrconf:subjattr_conf SubjAttrConf SubjAttr

definition subjattr_subjid::"SubjAttr\<Rightarrow>ResrcId" where
"subjattr_subjid sattr\<equiv>presrc_id(subj_resrcattr sattr)"

primrec find_subjid::"SubjAttrConf\<Rightarrow>SubjAttr\<Rightarrow>bool" where
"find_subjid nosubjattrconf sattr=False"
| "find_subjid (subjattr_conf conf sattrx) sattr=
(if subjattr_subjid sattrx=subjattr_subjid sattr
then
True
else find_subjid conf sattr)"

primrec delete_subjattr::"SubjAttrConf\<Rightarrow>SubjAttr\<Rightarrow>SubjAttrConf" where
"delete_subjattr nosubjattrconf sattr=nosubjattrconf"
| "delete_subjattr (subjattr_conf conf sattrx) sattr=
(if subjattr_subjid sattrx=subjattr_subjid sattr
then
delete_subjattr conf sattr
else subjattr_conf(delete_subjattr conf sattr) sattrx)"

primrec get_subjattr::"SubjAttrConf\<Rightarrow>ResrcId\<Rightarrow>SubjAttr" where
"get_subjattr nosubjattrconf rid=nosubjattr"
| "get_subjattr (subjattr_conf conf sattr) rid=
(if subjattr_subjid sattr=rid
then
sattr
else get_subjattr conf rid)"

primrec subjattrconf_uniq::"SubjAttrConf\<Rightarrow>bool" where
"subjattrconf_uniq nosubjattrconf=False"
| "subjattrconf_uniq (subjattr_conf conf sattr)=
(if subjattr_subjid sattr\<noteq>noresrcid\<and>
    conf=nosubjattrconf
then
True
else if subjattr_subjid sattr\<noteq>noresrcid\<and>
        (\<not>find_subjid conf sattr)\<and>
        subjattrconf_uniq conf
then
True
else False)"

primrec valid_subjattrconf::"SubjAttrConf\<Rightarrow>bool" where
"valid_subjattrconf nosubjattrconf=False"
|"valid_subjattrconf (subjattr_conf conf sattr)=
(if conf=nosubjattrconf\<and>
    sattr\<noteq>nosubjattr\<and>
    info_type(subj_resrcattr sattr)=Func
then
True
else if conf\<noteq>nosubjattrconf\<and>
        sattr\<noteq>nosubjattr\<and>
        info_type(subj_resrcattr sattr)=Func\<and>
        (\<not>find_subjid conf sattr)\<and>
        subjattrconf_uniq conf
then
True
else False)"

interpretation SubjAttrConf : SubjAttrConf nousrid valid_usrid noresrcid valid_resrcid noinfoid 
                                           valid_infoid InSgx OutSgx is_insgx Device Normal 
                                           is_normal Data Func is_data noresrcattr resrc_attr 
                                           presrc_id info_id trust_level presrc_type
                                           info_type nousrattr usr_attr usrattr_id
                                           nousrattrconf usrattr_conf is_usrattrconf find_usrid
                                           delete_usrattr get_usrattr valid_usrattrconf nosubjattr
                                           subj_attr subj_callerattr
                                           subj_participants subj_resrcattr nosubjattrconf
                                           subjattr_conf is_subjattrconf subjattr_subjid 
                                           find_subjid delete_subjattr get_subjattr 
                                           subjattrconf_uniq valid_subjattrconf
proof
  show "\<not> is_subjattrconf nosubjattrconf" by auto
next
  fix conf
  fix attr
  show "is_subjattrconf (subjattr_conf conf attr)" by auto
next
  fix x
  show "x = nosubjattrconf \<or>
        (\<exists>conf attr. x = subjattr_conf conf attr)"
  proof (cases x)
    assume "x = nosubjattrconf"
    from this show " x = nosubjattrconf \<or> (\<exists>conf attr. x = subjattr_conf conf attr)" by auto
  next
    fix x21
    fix x22
    assume "x = subjattr_conf x21 x22"
    from this show "x = nosubjattrconf \<or>
                   (\<exists>conf attr. x = subjattr_conf conf attr)" by auto
  qed
next
  show "subjattr_subjid nosubjattr = noresrcid" 
    by (auto simp add:subjattr_subjid_def nosubjattr_def noresrcattr_def)
next
  fix attr
  show "\<not> find_subjid nosubjattrconf attr" by auto
next
  fix attrx
  fix attr
  fix conf
  show "subjattr_subjid attrx = subjattr_subjid attr \<Longrightarrow>
       find_subjid (subjattr_conf conf attrx) attr" 
    by auto
next
  fix conf
  fix attrx
  fix attr
  show "find_subjid conf attr \<Longrightarrow>
       find_subjid (subjattr_conf conf attrx) attr" by auto
next
  fix conf
  fix attrx
  fix attr
  show "\<not> find_subjid conf attr \<and>
       subjattr_subjid attrx \<noteq> subjattr_subjid attr \<Longrightarrow>
       \<not> find_subjid (subjattr_conf conf attrx) attr" by auto
next
  fix attr
  show "delete_subjattr nosubjattrconf attr = nosubjattrconf" by auto
next
  fix attrx
  fix attr
  fix conf
  show "subjattr_subjid attrx = subjattr_subjid attr \<Longrightarrow>
       delete_subjattr (subjattr_conf conf attrx) attr =
       delete_subjattr conf attr" by auto
next
  fix attrx
  fix attr
  fix conf
  show "subjattr_subjid attrx \<noteq> subjattr_subjid attr \<Longrightarrow>
       delete_subjattr (subjattr_conf conf attrx) attr =
       subjattr_conf (delete_subjattr conf attr) attrx" by auto
next
  fix elem
  show "get_subjattr nosubjattrconf elem = nosubjattr" by auto
next
  fix attr 
  fix elem
  fix conf
  show "subjattr_subjid attr = elem \<Longrightarrow>
       get_subjattr (subjattr_conf conf attr) elem = attr" by auto
next
  fix elem
  fix attr
  fix conf
  show "subjattr_subjid attr \<noteq> elem \<Longrightarrow>
       get_subjattr (subjattr_conf conf attr) elem =
       get_subjattr conf elem" by auto
next
  show "\<not> subjattrconf_uniq nosubjattrconf" by auto
next
  fix conf
  fix attr
  show "subjattr_subjid attr \<noteq> noresrcid \<and> conf = nosubjattrconf \<Longrightarrow>
       subjattrconf_uniq (subjattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "subjattrconf_uniq conf \<and>
       \<not> find_subjid conf attr \<and> subjattr_subjid attr \<noteq> noresrcid \<Longrightarrow>
       subjattrconf_uniq (subjattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "subjattr_subjid attr = noresrcid \<Longrightarrow>
       \<not> subjattrconf_uniq (subjattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "conf \<noteq> nosubjattrconf \<and> \<not> subjattrconf_uniq conf \<Longrightarrow>
       \<not> subjattrconf_uniq (subjattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "conf \<noteq> nosubjattrconf \<and> find_subjid conf attr \<Longrightarrow>
       \<not> subjattrconf_uniq (subjattr_conf conf attr)" by auto
next
  show "\<And>P conf.
       P nosubjattrconf \<Longrightarrow>
       (\<And>conf1 attr1. P conf1 \<Longrightarrow> P (subjattr_conf conf1 attr1)) \<Longrightarrow>
       P conf"
  proof (erule SubjAttrConf.induct)
    show "\<And>P conf x1 x2.
         (\<And>conf1 attr1. P conf1 \<Longrightarrow> P (subjattr_conf conf1 attr1)) \<Longrightarrow>
         P x1 \<Longrightarrow> P (subjattr_conf x1 x2)" by auto
  qed
next
  fix sattr
  show "subjattr_subjid sattr = presrc_id (subj_resrcattr sattr)" 
    by (auto simp:subjattr_subjid_def)
next
  show "\<not> valid_subjattrconf nosubjattrconf" by auto
next
  fix conf
  fix sattr
  show "conf = nosubjattrconf \<and>
       sattr \<noteq> nosubjattr \<and>
       info_type (subj_resrcattr sattr) = InfoType.Func \<Longrightarrow>
       valid_subjattrconf (subjattr_conf conf sattr)" by auto
next
  fix conf
  fix sattr
  show "conf = nosubjattrconf \<and>
       sattr = nosubjattr \<and>
       info_type (subj_resrcattr sattr) = InfoType.Func \<Longrightarrow>
       \<not> valid_subjattrconf (subjattr_conf conf sattr)" by auto
next
  fix conf
  fix sattr
  show "conf = nosubjattrconf \<and>
       sattr \<noteq> nosubjattr \<and>
       info_type (subj_resrcattr sattr) \<noteq> InfoType.Func \<Longrightarrow>
       \<not> valid_subjattrconf (subjattr_conf conf sattr)" by auto
next
  fix conf
  fix sattr
  show "conf \<noteq> nosubjattrconf \<and>
       sattr \<noteq> nosubjattr \<and>
       info_type (subj_resrcattr sattr) = InfoType.Func \<and>
       \<not> find_subjid conf sattr \<and> subjattrconf_uniq conf \<Longrightarrow>
       valid_subjattrconf (subjattr_conf conf sattr)" by auto
next
  fix conf
  fix sattr
  show "conf \<noteq> nosubjattrconf \<and> sattr = nosubjattr \<Longrightarrow>
       \<not> valid_subjattrconf (subjattr_conf conf sattr)" by auto
next
  fix conf
  fix sattr
  show "conf \<noteq> nosubjattrconf \<and>
       sattr \<noteq> nosubjattr \<and>
       info_type (subj_resrcattr sattr) \<noteq> InfoType.Func \<and>
       \<not> find_subjid conf sattr \<and> subjattrconf_uniq conf \<Longrightarrow>
       \<not> valid_subjattrconf (subjattr_conf conf sattr)" by auto
next
  fix conf
  fix sattr
  show "conf \<noteq> nosubjattrconf \<and>
       sattr \<noteq> nosubjattr \<and>
       info_type (subj_resrcattr sattr) = InfoType.Func \<and>
       find_subjid conf sattr \<and> subjattrconf_uniq conf \<Longrightarrow>
       \<not> valid_subjattrconf (subjattr_conf conf sattr)" by auto
next
  fix conf
  fix sattr
  show "conf \<noteq> nosubjattrconf \<and>
       sattr \<noteq> nosubjattr \<and>
       info_type (subj_resrcattr sattr) = InfoType.Func \<and>
       \<not> find_subjid conf sattr \<and> \<not> subjattrconf_uniq conf \<Longrightarrow>
       \<not> valid_subjattrconf (subjattr_conf conf sattr)" by auto
qed

datatype ObjAttrConf = noobjattrconf |
                       is_objattrconf:objattr_conf ObjAttrConf ObjAttr

definition objattr_objid::"ObjAttr\<Rightarrow>ResrcId" where
"objattr_objid oattr\<equiv>presrc_id(obj_resrcattr oattr)"

primrec find_objid::"ObjAttrConf\<Rightarrow>ObjAttr\<Rightarrow>bool" where
"find_objid noobjattrconf oattr=False"
| "find_objid (objattr_conf conf oattrx) oattr=
(if objattr_objid oattrx=objattr_objid oattr
then
True
else find_objid conf oattr)"

primrec delete_objattr::"ObjAttrConf\<Rightarrow>ObjAttr\<Rightarrow>ObjAttrConf" where
"delete_objattr noobjattrconf oattr=noobjattrconf"
| "delete_objattr (objattr_conf conf oattrx) oattr=
(if objattr_objid oattrx=objattr_objid oattr
then
delete_objattr conf oattr
else 
objattr_conf(delete_objattr conf oattr) oattrx)"

primrec get_objattr::"ObjAttrConf\<Rightarrow>ResrcId\<Rightarrow>ObjAttr" where
"get_objattr noobjattrconf rid=noobjattr"
| "get_objattr (objattr_conf conf oattr) rid=
(if objattr_objid oattr=rid
then
oattr
else
get_objattr conf rid)"

primrec valid_objattrconf::"ObjAttrConf\<Rightarrow>bool" where
"valid_objattrconf noobjattrconf=False"
| "valid_objattrconf (objattr_conf conf oattr)=
(if objattr_objid oattr\<noteq>noresrcid\<and>
    conf=noobjattrconf
then
True
else if objattr_objid oattr\<noteq>noresrcid\<and>
        (\<not>find_objid conf oattr)\<and>
        valid_objattrconf conf
then
True
else False)"

interpretation ObjAttrConf : ObjAttrConf noresrcid valid_resrcid noinfoid valid_infoid InSgx 
                                         OutSgx is_insgx Device Normal is_normal Data Func is_data
                                         noresrcattr resrc_attr presrc_id info_id trust_level 
                                         presrc_type info_type nousrid valid_usrid nousrattr 
                                         usr_attr usrattr_id nousrattrconf usrattr_conf 
                                         is_usrattrconf find_usrid delete_usrattr get_usrattr 
                                         valid_usrattrconf noobjattr obj_attr 
                                         obj_owners obj_resrcattr noobjattrconf objattr_conf
                                         is_objattrconf objattr_objid find_objid delete_objattr
                                         get_objattr valid_objattrconf
proof
  show "\<not> is_objattrconf noobjattrconf" by auto
next
  fix conf
  fix attr
  show "is_objattrconf (objattr_conf conf attr)" by auto
next
  fix x
  show "x = noobjattrconf \<or>
       (\<exists>conf attr. x = objattr_conf conf attr)"
  proof (cases x)
    assume "x = noobjattrconf"
    from this show "x = noobjattrconf \<or> (\<exists>conf attr. x = objattr_conf conf attr)" by auto
  next
    fix x21
    fix x22
    assume "x = objattr_conf x21 x22"
    from this show "x = noobjattrconf \<or>
                   (\<exists>conf attr. x = objattr_conf conf attr)" by auto
  qed
next
  show "objattr_objid noobjattr = noresrcid" 
    by (auto simp:objattr_objid_def noobjattr_def noresrcattr_def)
next
  fix attr
  show "\<not> find_objid noobjattrconf attr" by auto
next
  fix conf
  fix attrx
  fix attr
  show "objattr_objid attrx = objattr_objid attr \<Longrightarrow>
       find_objid (objattr_conf conf attrx) attr" by auto
next
  fix conf
  fix attrx
  fix attr
  show "find_objid conf attr \<Longrightarrow> find_objid (objattr_conf conf attrx) attr" by auto
next
  fix conf
  fix attrx
  fix attr
  show "\<not> find_objid conf attr \<and>
       objattr_objid attrx \<noteq> objattr_objid attr \<Longrightarrow>
       \<not> find_objid (objattr_conf conf attrx) attr" by auto
next
  fix attr
  show "delete_objattr noobjattrconf attr = noobjattrconf" by auto
next
  fix attrx
  fix attr
  fix conf
  show "objattr_objid attrx = objattr_objid attr \<Longrightarrow>
       delete_objattr (objattr_conf conf attrx) attr =
       delete_objattr conf attr" by auto
next
  fix attrx
  fix attr
  fix conf
  show "objattr_objid attrx \<noteq> objattr_objid attr \<Longrightarrow>
       delete_objattr (objattr_conf conf attrx) attr =
       objattr_conf (delete_objattr conf attr) attrx" by auto
next
  fix elem
  show "get_objattr noobjattrconf elem = noobjattr" by auto
next
  fix attr
  fix elem
  fix conf
  show "objattr_objid attr = elem \<Longrightarrow>
       get_objattr (objattr_conf conf attr) elem = attr" by auto
next
  fix elem
  fix attr
  fix conf
  show "objattr_objid attr \<noteq> elem \<Longrightarrow>
       get_objattr (objattr_conf conf attr) elem = get_objattr conf elem" by auto
next
  show "\<not> valid_objattrconf noobjattrconf" by auto
next
  fix conf
  fix attr
  show "objattr_objid attr \<noteq> noresrcid \<and> conf = noobjattrconf \<Longrightarrow>
       valid_objattrconf (objattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "valid_objattrconf conf \<and>
       \<not> find_objid conf attr \<and> objattr_objid attr \<noteq> noresrcid \<Longrightarrow>
       valid_objattrconf (objattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "objattr_objid attr = noresrcid \<Longrightarrow>
       \<not> valid_objattrconf (objattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "conf \<noteq> noobjattrconf \<and> \<not> valid_objattrconf conf \<Longrightarrow>
       \<not> valid_objattrconf (objattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "conf \<noteq> noobjattrconf \<and> find_objid conf attr \<Longrightarrow>
       \<not> valid_objattrconf (objattr_conf conf attr)" by auto
next
  show "\<And>P conf.
       P noobjattrconf \<Longrightarrow>
       (\<And>conf1 attr1. P conf1 \<Longrightarrow> P (objattr_conf conf1 attr1)) \<Longrightarrow>
       P conf"
  proof (erule ObjAttrConf.induct)
    show "\<And>P conf x1 x2.
         (\<And>conf1 attr1. P conf1 \<Longrightarrow> P (objattr_conf conf1 attr1)) \<Longrightarrow>
         P x1 \<Longrightarrow> P (objattr_conf x1 x2)" by auto
  qed
next
  fix oattr
  show "objattr_objid oattr = presrc_id (obj_resrcattr oattr)"
    by (auto simp:objattr_objid_def)
qed

end
