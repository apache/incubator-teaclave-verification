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

theory I_AttrConf
  imports Main "../AttrConf" I_UsrAttr
begin

datatype UsrAttrConf = nousrattrconf |
                       is_usrattrconf:usrattr_conf UsrAttrConf UsrAttr

print_theorems

primrec find_usrid::"UsrAttrConf\<Rightarrow>UsrAttr\<Rightarrow>bool" where
"find_usrid nousrattrconf attr= False"
| "find_usrid (usrattr_conf conf attrx) attr=
(if usrattr_id attrx=usrattr_id attr
then
True
else find_usrid conf attr)"

primrec delete_usrattr::"UsrAttrConf\<Rightarrow>UsrAttr\<Rightarrow>UsrAttrConf" where
"delete_usrattr nousrattrconf attr=nousrattrconf"
| "delete_usrattr (usrattr_conf conf attrx) attr=
(if usrattr_id attrx=usrattr_id attr
then
delete_usrattr conf attr
else if usrattr_id attrx\<noteq>usrattr_id attr
then usrattr_conf(delete_usrattr conf attr) attrx
else usrattr_conf conf attrx)"

primrec get_usrattr::"UsrAttrConf\<Rightarrow>UsrId\<Rightarrow>UsrAttr" where
"get_usrattr nousrattrconf uid=nousrattr"
| "get_usrattr (usrattr_conf conf attr) uid=
(if usrattr_id attr=uid
then
attr
else if usrattr_id attr\<noteq>uid
then
get_usrattr conf uid
else nousrattr)"

primrec valid_usrattrconf::"UsrAttrConf\<Rightarrow>bool" where
"valid_usrattrconf nousrattrconf=False"
| "valid_usrattrconf (usrattr_conf conf attr)=
(if usrattr_id attr\<noteq>nousrid\<and>
    conf=nousrattrconf
then
True
else if usrattr_id attr\<noteq>nousrid\<and>
        (\<not>find_usrid conf attr)\<and>
        valid_usrattrconf conf
then
True
else False)"

primrec rel_subset_usr::"UsrAttrConf\<Rightarrow>UsrAttrConf\<Rightarrow>bool" where
"rel_subset_usr conf1 nousrattrconf=True" |
"rel_subset_usr conf1 (usrattr_conf conf attr)=
(if conf=nousrattrconf\<and>
    find_usrid conf1 attr
then
True
else if conf\<noteq>nousrattrconf\<and>
        find_usrid conf1 attr
then
rel_subset_usr conf1 conf
else False)"


interpretation UsrAttrConf : UsrAttrConf nousrid valid_usrid nousrattr usr_attr usrattr_id
                                         nousrattrconf usrattr_conf is_usrattrconf find_usrid
                                         delete_usrattr get_usrattr valid_usrattrconf
proof
  show "\<not> is_usrattrconf nousrattrconf" by auto
next
  fix conf
  fix attr
  show "is_usrattrconf (usrattr_conf conf attr)" by auto
next
  fix x
  show " x = nousrattrconf \<or>
         (\<exists>conf attr. x = usrattr_conf conf attr)"
  proof (cases x)
    show "x = nousrattrconf \<Longrightarrow>
    x = nousrattrconf \<or> (\<exists>conf attr. x = usrattr_conf conf attr)" by auto
  next
    fix x21
    fix x22
    show "x = usrattr_conf x21 x22 \<Longrightarrow>
          x = nousrattrconf \<or>
          (\<exists>conf attr. x = usrattr_conf conf attr)" by auto
  qed
next
  show "usrattr_id nousrattr = nousrid" by (auto simp:nousrattr_def)
next
  fix attr
  show "\<not>find_usrid nousrattrconf attr" by auto
next
  fix conf
  fix attr
  fix attrx
  show "usrattr_id attrx = usrattr_id attr \<Longrightarrow>
       find_usrid (usrattr_conf conf attrx) attr" by auto
next
  fix conf
  fix attrx
  fix attr
  show "find_usrid conf attr \<Longrightarrow> 
       find_usrid (usrattr_conf conf attrx) attr" by auto
next
  fix conf attr attrx
  show "\<not> find_usrid conf attr \<and> 
       usrattr_id attrx \<noteq> usrattr_id attr \<Longrightarrow>
       \<not> find_usrid (usrattr_conf conf attrx) attr" by auto
next
  fix attr
  show "delete_usrattr nousrattrconf attr = nousrattrconf" by auto
next
  fix conf
  fix attrx
  fix attr
  show "usrattr_id attrx = usrattr_id attr \<Longrightarrow>
       delete_usrattr (usrattr_conf conf attrx) attr =
       delete_usrattr conf attr" by auto
next
  fix attrx
  fix attr
  fix conf
  show "usrattr_id attrx \<noteq> usrattr_id attr \<Longrightarrow>
       delete_usrattr (usrattr_conf conf attrx) attr =
       usrattr_conf (delete_usrattr conf attr) attrx" by auto
next
  fix elem
  show "get_usrattr nousrattrconf elem = nousrattr" by auto
next
  fix attr
  fix elem
  fix conf
  show "usrattr_id attr = elem \<Longrightarrow>
       get_usrattr (usrattr_conf conf attr) elem = attr" by auto
next
  fix elem
  fix attr
  fix conf
  show "get_usrattr conf elem = nousrattr \<and> 
       usrattr_id attr \<noteq> elem \<Longrightarrow>
       get_usrattr (usrattr_conf conf attr) elem = nousrattr" by auto
next
  fix conf
  fix elem
  fix attr
  show "get_usrattr conf elem \<noteq> nousrattr \<and> 
       usrattr_id attr \<noteq> elem \<Longrightarrow>
       get_usrattr (usrattr_conf conf attr) elem = get_usrattr conf elem" by auto
next
  show "\<not> valid_usrattrconf nousrattrconf" by auto
next
  fix conf
  fix attr
  show "usrattr_id attr \<noteq> nousrid \<and> conf = nousrattrconf \<Longrightarrow>
       valid_usrattrconf (usrattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "valid_usrattrconf conf \<and>
       \<not> find_usrid conf attr \<and> usrattr_id attr \<noteq> nousrid \<Longrightarrow>
       valid_usrattrconf (usrattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "usrattr_id attr = nousrid \<Longrightarrow>
       \<not> valid_usrattrconf (usrattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "conf \<noteq> nousrattrconf \<and> \<not> valid_usrattrconf conf \<Longrightarrow>
       \<not> valid_usrattrconf (usrattr_conf conf attr)" by auto
next
  fix conf
  fix attr
  show "conf \<noteq> nousrattrconf \<and> find_usrid conf attr \<Longrightarrow>
       \<not> valid_usrattrconf (usrattr_conf conf attr)" by auto
next
  show "\<And>P conf.
       P nousrattrconf \<Longrightarrow>
       (\<And>conf1 attr1. P conf1 \<Longrightarrow> P (usrattr_conf conf1 attr1)) \<Longrightarrow>
       P conf"
  proof (erule UsrAttrConf.induct)
    show "\<And>P conf x1 x2.
       (\<And>conf1 attr1. P conf1 \<Longrightarrow> P (usrattr_conf conf1 attr1)) \<Longrightarrow>
       P x1 \<Longrightarrow> P (usrattr_conf x1 x2)" by auto
  qed
qed

interpretation UsrAttrConfRel : AttrConfRel nousrid nousrattr nousrattrconf usrattr_conf is_usrattrconf 
                                usrattr_id find_usrid delete_usrattr get_usrattr valid_usrattrconf
                                rel_subset_usr
proof
  fix confx
  show "rel_subset_usr confx nousrattrconf" by auto
next
  fix conf
  fix confx
  fix attr
  show "conf = nousrattrconf \<and> find_usrid confx attr \<Longrightarrow>
       rel_subset_usr confx (usrattr_conf conf attr)" by auto
next
  fix conf
  fix confx
  fix attr
  show "conf \<noteq> nousrattrconf \<and>
       find_usrid confx attr \<and> rel_subset_usr confx conf \<Longrightarrow>
       rel_subset_usr confx (usrattr_conf conf attr)" by auto
next
  fix conf
  fix confx
  fix attr
  show "\<not> rel_subset_usr confx conf \<Longrightarrow>
       \<not> rel_subset_usr confx (usrattr_conf conf attr)" by auto
next
  fix confx
  fix conf
  fix attr
  show "rel_subset_usr confx conf \<and> \<not> find_usrid confx attr \<Longrightarrow>
       \<not> rel_subset_usr confx (usrattr_conf conf attr)" by auto
qed

end
